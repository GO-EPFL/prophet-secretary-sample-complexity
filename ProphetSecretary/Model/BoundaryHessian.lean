import ProphetSecretary.Model.BoundaryConditional
import ProphetSecretary.Model.DurationRegretExpectation
import ProphetSecretary.Reach.SelectionChargeDiagonal
import ProphetSecretary.Reach.CrossingNull
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Averaged finite boundary Hessian

Actual uniform-clock replacement, the finite-state triangular expansion, and
dominated convergence identify the second-order fixed-policy scalar regret.
The limiting coefficient is charged to at most one selected identity in mean.
-/

open MeasureTheory Set Filter
open scoped Classical Topology BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.meanBoundaryCharge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 < z) : ℝ :=
  ∫ ω : World n Unit, ∑ i : Fin n, ∑ A : Finset (Fin n),
    P.crossingSelectionCharge hP i hz (ω.1 i) A ω ∂P.worldLaw (Measure.dirac ())

lemma Instance.meanBoundaryCharge_le_one (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 < z) : P.meanBoundaryCharge hP hz ≤ 1 :=
  P.mean_total_crossingSelectionCharge_le_one hP hz

lemma Instance.meanBoundaryCharge_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 < z) : 0 ≤ P.meanBoundaryCharge hP hz := by
  apply integral_nonneg
  intro ω
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro A _
  unfold Instance.crossingSelectionCharge
  split_ifs
  · exact mul_nonneg (sq_nonneg _) ((P.restrictTo A).rootDuration_mem_unitInterval _ _).1
  · exact le_rfl

/-- Conditional quadratic regret can be averaged over the actual residual law.
The endpoint exclusion is later supplied for almost every normalized weight. -/
theorem Instance.mean_conditionalDurationRegret_limit (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (hr0 : ∀ᵐ ω : World n Unit ∂P.worldLaw (Measure.dirac ()), ∀ A : Finset (Fin n),
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (ω.1 i) ≠ 0) :
    Tendsto (fun h : ℝ ↦ ∫ ω : World n Unit,
      P.conditionalDurationRegret (P.valuePolicy hP zero_le_one hz.le).rule z (z + h) ω.1 ω.2.1 i / h ^ 2
        ∂P.worldLaw (Measure.dirac ())) (𝓝[≠] 0)
      (𝓝 (∫ ω : World n Unit, (∑ A : Finset (Fin n), P.crossingSelectionCharge hP i hz (ω.1 i) A ω) / (2 * z)
        ∂P.worldLaw (Measure.dirac ()))) := by
  let π : Policy Unit n := (P.valuePolicy hP zero_le_one hz.le).rule
  have hπ : π.IsMeasurable := (P.valuePolicy hP zero_le_one hz.le).measurable_rule
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : World n Unit ↦ 16 * (1 + (n : ℝ)) / z)
  · have hc : Continuous (fun h : ℝ ↦ z + h) := continuous_const.add continuous_id
    have hpos : ∀ᶠ h : ℝ in 𝓝 0, 0 < z + h :=
      (show Tendsto (fun h : ℝ ↦ z + h) (𝓝 0) (𝓝 z) by simpa only [add_zero] using hc.tendsto 0)
        (Ioi_mem_nhds hz)
    filter_upwards [hpos.filter_mono nhdsWithin_le_nhds] with h hh
    exact (P.measurable_conditionalDurationRegret hP π hπ hz.le hh.le i).div_const (h ^ 2) |>.aestronglyMeasurable
  · filter_upwards [P.eventually_conditionalDurationRegret_bound hP π hz] with h hh
    exact Filter.Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hh ω.1 ω.2.1 i)
  · exact integrable_const _
  · filter_upwards [hr0, P.all_crossingTimes_ne_clocks_ae hP (Measure.dirac ()) z] with ω hω hc
    exact P.conditionalDurationRegret_limit hP i hz ω hω (fun A j _ ↦ hc i A j)

/-- Actual fixed-base-policy boundary-Hessian formula in duration coordinates. -/
theorem Instance.durationRegret_limit (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 < z)
    (hr0 : ∀ᵐ ω : World n Unit ∂P.worldLaw (Measure.dirac ()), ∀ (i : Fin n) (A : Finset (Fin n)),
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (ω.1 i) ≠ 0) :
    Tendsto (fun h : ℝ ↦ (optimalScalarValue P 1 (z + h) -
      (P.valuePolicy hP zero_le_one hz.le).scalarObjective P 1 (z + h)) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (P.meanBoundaryCharge hP hz / (2 * z))) := by
  have hSum := tendsto_finsetSum Finset.univ (fun i _ ↦ P.mean_conditionalDurationRegret_limit hP i hz
    (hr0.mono (fun ω hω ↦ hω i)))
  have hLimit : (∑ i : Fin n, ∫ ω : World n Unit,
      (∑ A : Finset (Fin n), P.crossingSelectionCharge hP i hz (ω.1 i) A ω) / (2 * z)
        ∂P.worldLaw (Measure.dirac ())) = P.meanBoundaryCharge hP hz / (2 * z) := by
    simp_rw [integral_div]
    rw [← Finset.sum_div]
    congr 1
    exact (integral_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum _
      (fun A _ ↦ P.integrable_crossingSelectionCharge_diagonal hP i hz A))).symm
  rw [hLimit] at hSum
  apply hSum.congr'
  have hc : Continuous (fun h : ℝ ↦ z + h) := continuous_const.add continuous_id
  have hpos : ∀ᶠ h : ℝ in 𝓝 0, 0 < z + h :=
    (show Tendsto (fun h : ℝ ↦ z + h) (𝓝 0) (𝓝 z) by simpa only [add_zero] using hc.tendsto 0)
      (Ioi_mem_nhds hz)
  filter_upwards [hpos.filter_mono nhdsWithin_le_nhds] with h hh
  rw [P.durationRegret_eq_mean_conditional hP hz.le hh.le, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_div (h ^ 2) _

end ProphetSecretary.Model
