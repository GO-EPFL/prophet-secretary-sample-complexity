import ProphetSecretary.Statistics.MixedFixedScalarContributions
import ProphetSecretary.Statistics.MixedEmpiricalClockResidual
import ProphetSecretary.Statistics.MixedEmpiricalJointMoments

/-!
# Fixed-weight upward bias with exact known marginals

The true canonical optimizer is fixed before training. Its TRUE-online cross-law
Bellman identity splits upward bias into the centered reached mixed residual and
nonnegative mixed-design action loss. Actual reach dropping, three-law candidate
integration and the proved true-candidate rate give the original constant.
No centering is asserted for a sample-selected scalar.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

lemma integrable_mixedScalarValue_reservoir (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z : ℝ} (hz : 0≤z) :
    Integrable (fun y : Reservoir n k => optimalScalarValue (mixedEmpiricalInstance P known y) 1 z) (P.reservoirLaw k) := by
  have hY : ∀ᵐ y ∂P.reservoirLaw k, ∀ i l, y i l≤1 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun l =>
      (P.reservoir_coordinate_measurePreserving k i l).quasiMeasurePreserving.ae (hbound i)
  simpa only [pow_one] using integrable_mixedScalarValue_pow_unit P hbound known (P.reservoirLaw k)
    (y:=fun y => y) (c:=fun _ => z) (C:=z)
    (fun i l => (measurable_pi_apply l).comp (measurable_pi_apply i)) measurable_const (fun _ => hz)
    (Eventually.of_forall fun _ => le_rfl) hY 1

theorem mixedScalarValue_expected_optimism_bound (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z lo hi : ℝ}
    (hlo : 0<lo) (hlohi : lo≤hi) (hz : z∈Icc lo hi) :
    0 ≤ (∫ a : (Fin n × Fin k) → ℝ,
      optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z ∂P.trainingCoordinateLaw k)-
        optimalScalarValue P 1 z ∧
    (∫ a : (Fin n × Fin k) → ℝ,
      optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z ∂P.trainingCoordinateLaw k)-
        optimalScalarValue P 1 z ≤
      empiricalCandidateRegretConstant lo hi*P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ) := by
  have hz0 := (hlo.trans_le hz.1).le
  have hP := P.integrable_maximum_of_bounded hbound
  let π := P.valuePolicy hP zero_le_one hz0
  let μ := P.trainingCoordinateLaw k
  let V : ((Fin n × Fin k) → ℝ) → ℝ := fun a => optimalScalarValue (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) 1 z
  let R : ((Fin n × Fin k) → ℝ) → ℝ := fun a => ∫ u, π.mixedClockResidual P known z (a,u) ∂Instance.clocksLaw n
  let A : ((Fin n × Fin k) → ℝ) → ℝ := fun a => V a-optimalScalarValue P 1 z-R a
  have hVI : Integrable V μ := by
    simpa only [pow_one] using mixedScalarValue_integrable_pow (k:=k) P known hbound hz0 1
  have hRI : Integrable R μ := (π.integrable_mixedClockResidual (k:=k) P known hbound hz0).integral_prod_left
  have hSub : Integrable (fun a => V a-optimalScalarValue P 1 z) μ := hVI.sub (integrable_const _)
  have hAI : Integrable A μ := hSub.sub hRI
  have hEq (a : (Fin n × Fin k) → ℝ) : A a =
      π.expectedReachedDesignActionLoss (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) P 1 z := by
    let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm a)
    have hQ := mixedEmpiricalInstance_integrable P hP known (reservoirCoordinates.symm a)
    have h := π.bellman_residualIdentity_clocks Q P hQ hP zero_lt_one hz0
    have hOpt : π.scalarObjective P 1 z=optimalScalarValue P 1 z := P.valuePolicy_optimal hP zero_lt_one hz0
    rw [hOpt] at h
    change V a-optimalScalarValue P 1 z=R a+π.expectedReachedDesignActionLoss Q P 1 z at h
    dsimp only [A]
    linarith only [h]
  have hA0 (a) : 0≤A a := by
    rw [hEq]
    exact π.expectedReachedDesignActionLoss_nonnegative _ P 1 z
  have hUpper (a) : A a≤∑ i : Fin n, fixedScalarMixedCandidateContribution P known z true i a := by
    rw [hEq]
    exact trueCanonical_mixedDesignActionLoss_le_candidates P hP known a hz0
  have hCI (i : Fin n) := integrable_fixedScalarMixedCandidateContribution (k:=k) P known hbound hz0 hz.2 true i
  have hSumI : Integrable (fun a => ∑ i : Fin n, fixedScalarMixedCandidateContribution P known z true i a) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hCI i)
  have hRzero : (∫ a, R a ∂μ)=0 := π.integral_mixedClockResidual_zero P known hbound hz0
  have hAmean : (∫ a, A a ∂μ)=(∫ a, V a ∂μ)-optimalScalarValue P 1 z := by
    change (∫ a, (V a-optimalScalarValue P 1 z)-R a ∂μ)=_
    rw [integral_sub (f:=fun a => V a-optimalScalarValue P 1 z) (g:=R) hSub hRI,
      integral_sub hVI (integrable_const _),integral_const,probReal_univ,one_smul,hRzero,sub_zero]
  have hLo : 0≤∫ a, A a ∂μ := integral_nonneg hA0
  have hHi := integral_mono hAI hSumI hUpper
  rw [hAmean] at hLo hHi
  rw [integral_finsetSum _ (fun i _ => hCI i)] at hHi
  exact ⟨hLo,hHi.trans (sum_integral_fixedScalarMixedCandidateContribution_rate P known hbound hlo hlohi hz true)⟩

/-- The same actual fixed-weight assertion in the paper's training-array coordinates. -/
theorem mixedScalarValue_expected_optimism_bound_reservoir (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z lo hi : ℝ}
    (hlo : 0<lo) (hlohi : lo≤hi) (hz : z∈Icc lo hi) :
    0 ≤ (∫ y : Reservoir n k, optimalScalarValue (mixedEmpiricalInstance P known y) 1 z ∂P.reservoirLaw k)-
      optimalScalarValue P 1 z ∧
    (∫ y : Reservoir n k, optimalScalarValue (mixedEmpiricalInstance P known y) 1 z ∂P.reservoirLaw k)-
      optimalScalarValue P 1 z ≤
      empiricalCandidateRegretConstant lo hi*P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ) := by
  have he := (P.reservoirCoordinates_symm_measurePreserving k).integral_comp'
    (fun y : Reservoir n k => optimalScalarValue (mixedEmpiricalInstance P known y) 1 z)
  rw [←he]
  exact mixedScalarValue_expected_optimism_bound P known hbound hlo hlohi hz

end ProphetSecretary.Model
