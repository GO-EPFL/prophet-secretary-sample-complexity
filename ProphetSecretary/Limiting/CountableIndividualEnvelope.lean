import ProphetSecretary.Limiting.CountableIndividualLikelihood
import ProphetSecretary.Limiting.CountableCanonicalLimit
import ProphetSecretary.Analysis.StableEnvelope

/-!
# The individual-likelihood envelope in the full limiting model

The complete-value score is analytical. Exact fixed-policy likelihood
identities are established before the optimized value is differentiated.
The common policy index class is the full admissible class, identified by
actual mutual absolute continuity of the observation laws.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Limiting
open CountableInstance

lemma RandomizedCountablePolicy.scalarIndividualLikelihoodDerivative_bound {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (i : ℕ) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    {h : ℝ → ℝ} (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1) :
    |π.scalarIndividualLikelihoodDerivative i w c h| ≤ w*(B.cap : ℝ)+c := by
  have hNorm : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw,
      ‖π.scalarPayoff w c v*h (v.2.1 i)‖ ≤ w*(B.cap : ℝ)+c := by
    filter_upwards [π.scalarPayoff_bounded hw hc,B.individualScore_bounded_ae π.seedLaw i hb] with v hv hZ
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hv.1]
    exact (mul_le_mul hv.2 hZ (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have h := norm_integral_le_of_norm_le_const hNorm
  simpa only [scalarIndividualLikelihoodDerivative,Real.norm_eq_abs,probReal_univ,mul_one] using h

lemma RandomizedCountablePolicy.scalarIndividualLikelihoodDerivative_difference_le {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (i : ℕ) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    {h : ℝ → ℝ} (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1) :
    |π.scalarIndividualLikelihoodDerivative i w c h-
      (B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i w c h| ≤
        (w+c)*π.expectedValueOutcomeError w c := by
  let π₀ := B.valuePolicy hw hc
  let F := fun v : CompleteWorld Unit => π₀.scalarPayoff w c v*h (v.2.1 i)
  have hF : Measurable F := (π₀.measurable_scalarPayoff w c).mul (measurable_individualScore i hh)
  have hFI : Integrable F (B.completeWorldLaw (Measure.dirac ())) :=
    π₀.integrable_scalarIndividualLikelihood i w c hh hb
  have hSeed := B.eraseCompleteSeed_measurePreserving π.seedLaw
  have hMean := hSeed.hasLaw.integral_comp hF.aestronglyMeasurable
  change (∫ v, F (eraseCompleteSeed v) ∂B.completeWorldLaw π.seedLaw)=
    π₀.scalarIndividualLikelihoodDerivative i w c h at hMean
  have hOldI := π.integrable_scalarIndividualLikelihood i w c hh hb
  have hBaseI : Integrable (fun v => F (eraseCompleteSeed v)) (B.completeWorldLaw π.seedLaw) :=
    hSeed.integrable_comp_of_integrable hFI
  have hDifference : π.scalarIndividualLikelihoodDerivative i w c h-
      π₀.scalarIndividualLikelihoodDerivative i w c h=
      ∫ v, (π.scalarPayoff w c v*h (v.2.1 i)-F (eraseCompleteSeed v)) ∂B.completeWorldLaw π.seedLaw := by
    rw [integral_sub hOldI hBaseI,hMean]
    rfl
  have hK : 0 ≤ w+c := add_nonneg hw.le hc.le
  have hNorm : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw,
      ‖π.scalarPayoff w c v*h (v.2.1 i)-F (eraseCompleteSeed v)‖ ≤
        (w+c)*π.rule.coupledValueOutcomeError B w c v := by
    filter_upwards [B.individualScore_bounded_ae π.seedLaw i hb] with v hZ
    let dR := π.rule.realizedReward B.terminal v-(B.valueRule w c).realizedReward B.terminal (eraseCompleteSeed v)
    let dT := π.rule.realizedDuration v-(B.valueRule w c).realizedDuration (eraseCompleteSeed v)
    have hCoef : |w*dR+c*dT| ≤ (w+c)*π.rule.coupledValueOutcomeError B w c v := by
      calc
        _ ≤ |w*dR|+|c*dT| := abs_add_le _ _
        _ = w*|dR|+c*|dT| := by rw [abs_mul,abs_mul,abs_of_pos hw,abs_of_pos hc]
        _ ≤ (w+c)*|dR|+(w+c)*|dT| := add_le_add
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hc.le) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hw.le) (abs_nonneg _))
        _ = _ := by change _=(w+c)*(|dR|+|dT|); ring
    have hEq : π.scalarPayoff w c v*h (v.2.1 i)-F (eraseCompleteSeed v)=
        (w*dR+c*dT)*h (v.2.1 i) := by
      dsimp only [RandomizedCountablePolicy.scalarPayoff,F,π₀,CountableInstance.valuePolicy,dR,dT,eraseCompleteSeed]
      ring
    rw [hEq,Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul hCoef hZ (abs_nonneg _)
      (mul_nonneg hK (π.rule.coupledValueOutcomeError_nonnegative B w c v))).trans_eq (mul_one _)
  have hBound := norm_integral_le_of_norm_le
    ((π.rule.integrable_coupledValueOutcomeError π.measurable_rule B π.seedLaw hw.le hc.le).const_mul (w+c)) hNorm
  rw [integral_const_mul] at hBound
  rw [hDifference]
  simpa only [Real.norm_eq_abs,RandomizedCountablePolicy.expectedValueOutcomeError] using hBound

/-- The individual-variable likelihood part of `lem:envelopes`, for a bounded
centered score. The derivative uses the fixed base-optimal policy. -/
theorem CountableInstance.hasDerivAt_optimalScalarValue_individualLikelihoodPath
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (i : ℕ) (h : ℝ → ℝ) (hh : Measurable h)
    (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) :
    HasDerivAt (fun θ => (B.individualLikelihoodPath i h hh hb hm θ).optimalScalarValue w c)
      ((B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i w c h) 0 := by
  let π₀ := B.valuePolicy hw hc
  let J := fun θ (π : RandomizedCountablePolicy B) =>
    (π.individualLikelihoodPolicy i h hh hb hm θ).scalarObjective w c
  let D := fun π : RandomizedCountablePolicy B => π.scalarIndividualLikelihoodDerivative i w c h
  have hZeroJ (π : RandomizedCountablePolicy B) : J 0 π=π.scalarObjective w c := by
    simpa only [J,zero_mul,add_zero] using π.individualLikelihoodPolicy_scalarObjective i h hh hb hm
      (by norm_num : |(0 : ℝ)| ≤ 1/4) w c
  have hBase : ∀ π, J 0 π ≤ J 0 π₀ := by
    intro π
    rw [hZeroJ,hZeroJ]
    exact (B.scalarObjective_le_value π w c).trans_eq (B.valuePolicy_optimal hZero hw hc).symm
  have hD : ∀ π, |D π| ≤ w*(B.cap : ℝ)+c := fun π =>
    π.scalarIndividualLikelihoodDerivative_bound i hw.le hc.le hb
  have hTaylor : ∀ θ, |θ| ≤ 1/4 → ∀ π,
      |J θ π-J 0 π-θ*D π| ≤ (0 : ℝ)*θ^2 := by
    intro θ hθ π
    have hT : J θ π=J 0 π+θ*D π := by
      rw [hZeroJ]
      exact π.individualLikelihoodPolicy_scalarObjective i h hh hb hm hθ w c
    have hEq : J θ π-J 0 π-θ*D π=0 := by linarith only [hT]
    rw [hEq]
    norm_num
  obtain ⟨Ω,_,hMono,_,hLimit,hError⟩ := B.outcome_stability hZero hw hc
  have hStable : ∀ ε, 0 < ε → ∃ η, 0 < η ∧
      ∀ π, J 0 π₀-J 0 π ≤ η → |D π-D π₀| ≤ ε := by
    intro ε hε
    have hLimitK : Tendsto (fun r => (w+c)*Ω r) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hLimit.const_mul (w+c)
    obtain ⟨η,hηSmall,hη⟩ := ((hLimitK.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
    refine ⟨η,hη,?_⟩
    intro π hNear
    have hRegret : B.optimalScalarValue w c-π.scalarObjective w c ≤ η := by
      rw [hZeroJ,hZeroJ,B.valuePolicy_optimal hZero hw hc] at hNear
      exact hNear
    have hBound := π.scalarIndividualLikelihoodDerivative_difference_le i hw hc hh hb
    have hMean := mul_le_mul_of_nonneg_left (hError π) (add_nonneg hw.le hc.le)
    have hRadius := mul_le_mul_of_nonneg_left (hMono hRegret) (add_nonneg hw.le hc.le)
    exact hBound.trans (hMean.trans (hRadius.trans hηSmall.le))
  have hDeriv := ProphetSecretary.Analysis.hasDerivAt_supremum_of_stable_payoffs J D π₀
    (by norm_num : (0 : ℝ) ≤ 0) (show 0 ≤ w*(B.cap : ℝ)+c by positivity)
    (by norm_num : (0 : ℝ) < 1/4) hBase hD hTaylor hStable
  have hSup (θ : ℝ) : (B.individualLikelihoodPath i h hh hb hm θ).optimalScalarValue w c=
      sSup (Set.range (J θ)) := by
    exact B.optimalScalarValue_eq_sSup_transport (B.individualLikelihoodPath i h hh hb hm θ)
      (fun π => B.individualLikelihoodPath_absolutelyContinuous i h hh hb hm θ π.seedLaw)
      (fun π => B.absolutelyContinuous_individualLikelihoodPath i h hh hb hm θ π.seedLaw) w c
  have hFunctions : (fun θ => sSup (Set.range (J θ)))=
      (fun θ => (B.individualLikelihoodPath i h hh hb hm θ).optimalScalarValue w c) :=
    funext (fun θ => (hSup θ).symm)
  rw [hFunctions] at hDeriv
  exact hDeriv

end ProphetSecretary.Limiting
