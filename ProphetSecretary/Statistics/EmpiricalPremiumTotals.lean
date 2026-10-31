import ProphetSecretary.Statistics.PremiumMean
import ProphetSecretary.Model.EmpiricalPolicy

/-!
# True-law premiums at empirical continuation thresholds

The paper's `U` integrates positive parts against the true marginals while retaining
the empirical design continuation. Its empirical counterpart is the unstopped premium
sum. Their difference is exactly the complete residual sum, without any statistical
centering assertion for selected weights.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.unstoppedPremiumUnder (Q P : Instance n) (w c : ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ i, positivePremium (P.law i) w (Q.continuationAtArrival w c (fun _ => 0) u i)

lemma Instance.unstoppedPremiumUnder_nonnegative (Q P : Instance n) (w c : ℝ) (u : Fin n → ℝ) :
    0 ≤ Q.unstoppedPremiumUnder P w c u := Finset.sum_nonneg (fun _ _ => positivePremium_nonnegative _ _ _)

lemma Instance.unstoppedPremiumUnder_eq_difference (Q P : Instance n) (w c : ℝ) (u : Fin n → ℝ) :
    Q.unstoppedPremiumUnder P w c u = Q.unstoppedPremium w c u - ∑ i, Q.transitionResidual P w c u i := by
  unfold Instance.unstoppedPremiumUnder Instance.unstoppedPremium Instance.clockPremium
    Instance.transitionResidual Instance.lawResidual
  rw [Finset.sum_sub_distrib]
  ring

lemma Instance.unstoppedPremiumUnder_le_firstMoment (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (u : Fin n → ℝ) :
    Q.unstoppedPremiumUnder P w c u ≤ w * P.totalFirstMoment := by
  calc
    _ ≤ ∑ i : Fin n, w * ∫ x, x ∂P.law i := by
      apply Finset.sum_le_sum
      intro i _
      exact positivePremium_le_firstMoment (P.law i) (P.integrable_maximum_iff.mp hP i) (P.nonnegative i) hw
        (Q.continuationAtArrival_nonnegative hQ hw hc _ u i)
    _ = _ := by simp only [Instance.totalFirstMoment, Finset.mul_sum]

variable {k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_empiricalContinuationAtArrival
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hu : ∀ i, Measurable fun ω => u ω i) (i : Fin n) :
    Measurable fun ω => (totalEmpiricalInstance (y ω)).continuationAtArrival 1 (c ω) (fun _ => 0) (u ω) i := by
  have hA := measurable_unseen.comp (measurable_history Finset.univ (x := fun _ : Ω => fun _ : Fin n => (0 : ℝ)) (fun _ => measurable_const) hu (hu i))
  have hθ := measurable_totalEmpirical_valueThreshold (w := fun _ => 1) (i := fun _ => i) hy measurable_const hc (hu i) hA measurable_const
    (fun _ => by norm_num) hc0
  convert hθ using 1
  funext ω
  simpa only [one_mul, Function.comp_def] using
    (totalEmpiricalInstance (y ω)).continuationAtArrival_eq_threshold (by norm_num : (0 : ℝ) < 1)
      (c ω) (fun _ => 0) (u ω) i

lemma Instance.measurable_empiricalPremiumUnder (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hu : ∀ i, Measurable fun ω => u ω i) :
    Measurable fun ω => (totalEmpiricalInstance (y ω)).unstoppedPremiumUnder P 1 (c ω) (u ω) := by
  apply Finset.measurable_sum
  intro i _
  exact (positivePremium_continuous (P.law i) (P.integrable_maximum_iff.mp hP i) 1).measurable.comp
    (measurable_empiricalContinuationAtArrival hy hc hc0 hu i)

/-- All powers are integrable under any probability parameter law. This also covers
measurable data-selected nonnegative coefficients, without asserting unbiasedness. -/
lemma Instance.integrable_empiricalPremiumUnder_pow (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Ω) [IsProbabilityMeasure ν]
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hu : ∀ i, Measurable fun ω => u ω i) (p : ℕ) :
    Integrable (fun ω => (totalEmpiricalInstance (y ω)).unstoppedPremiumUnder P 1 (c ω) (u ω) ^ p) ν := by
  have hm := (P.measurable_empiricalPremiumUnder hP hy hc hc0 hu).pow_const p
  apply Integrable.of_bound hm.aestronglyMeasurable (P.totalFirstMoment ^ p)
  filter_upwards [] with ω
  have h0 := (totalEmpiricalInstance (y ω)).unstoppedPremiumUnder_nonnegative P 1 (c ω) (u ω)
  have h1 : (totalEmpiricalInstance (y ω)).unstoppedPremiumUnder P 1 (c ω) (u ω) ≤ P.totalFirstMoment := by
    simpa only [one_mul] using (totalEmpiricalInstance (y ω)).unstoppedPremiumUnder_le_firstMoment P
      (totalEmpiricalInstance_integrable _) hP zero_le_one (hc0 ω) (u ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 p)]
  exact pow_le_pow_left₀ h0 h1 p

end ProphetSecretary.Model
