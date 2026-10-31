import ProphetSecretary.Limiting.CountableCanonicalLimit
import ProphetSecretary.Limiting.CountableScoreStability

/-!
# Score expectations along arbitrary canonical truncations

The retained prefix tends to infinity and the positive mark cutoff tends to
zero. Exact truncated-policy values first give vanishing regret in the full
instance. Actual outcome stability and the L² score estimate then give reward
and duration score convergence. The score may depend on offers after stopping;
it is an analytical variable, never an input supplied to the online policy.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open CountableInstance

lemma CountableInstance.CountableRule.integrable_score_products {B : CountableInstance}
    {Seed : Type*} [MeasurableSpace Seed] (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {Z : CompleteWorld Seed → ℝ}
    (hZ : MemLp Z 2 (B.completeWorldLaw ν)) :
    Integrable (fun v => Z v*π.realizedReward B.terminal v) (B.completeWorldLaw ν) ∧
    Integrable (fun v => Z v*π.realizedDuration v) (B.completeWorldLaw ν) := by
  have hZI : Integrable Z (B.completeWorldLaw ν) := MemLp.integrable (by norm_num : (1 : ENNReal)≤2) hZ
  constructor
  · apply hZI.mul_bdd (π.measurable_realizedReward hπ B.terminal).aestronglyMeasurable
    filter_upwards [π.reward_bounded B ν] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg hv.1]
    exact hv.2
  · apply hZI.mul_bdd (π.measurable_realizedDuration hπ).aestronglyMeasurable
    exact Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs,abs_of_nonneg (π.duration_bounds v).1]
      exact (π.duration_bounds v).2)

lemma CountableInstance.truncatedValuePolicy_outcomeError_tendsto (B : CountableInstance)
    (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal : ℝ)<bs m)
    (hNs : Tendsto Ns atTop atTop) (hbsLim : Tendsto bs atTop (𝓝 (B.terminal : ℝ))) :
    Tendsto (fun m => (B.truncatedValuePolicy (Ns m) (bs m) (hbs m) hw.le hc.le).expectedValueOutcomeError w c)
      atTop (𝓝 (0 : ℝ)) := by
  let π := fun m => B.truncatedValuePolicy (Ns m) (bs m) (hbs m) hw.le hc.le
  have hValue := B.truncation_value_tendsto Ns bs hbs hNs hbsLim hw.le hc.le
  have hRegret : Tendsto (fun m => B.optimalScalarValue w c-(π m).scalarObjective w c) atTop (𝓝 (0 : ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => B.optimalScalarValue w c) atTop (𝓝 (B.optimalScalarValue w c)) := tendsto_const_nhds
    have h := hConst.sub hValue
    simpa only [π,B.truncatedValuePolicy_scalarObjective hZero _ _ _ hw hc.le,sub_self] using h
  obtain ⟨Ω,_hΩ,hMono,_hΩZero,hLimit,hError⟩ := B.outcome_stability hZero hw hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η,hSmall,hη⟩ := ((hLimit.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  obtain ⟨m0,hm0⟩ := eventually_atTop.mp (hRegret.eventually (gt_mem_nhds hη))
  refine ⟨m0,fun m hm => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg ((π m).expectedValueOutcomeError_nonnegative w c)]
  exact lt_of_le_of_lt ((hError (π m)).trans (hMono (hm0 m hm).le)) hSmall

/-- Arbitrary prefix/cutoff paths preserve both complete-score expectations. -/
theorem CountableInstance.truncatedValueRule_scorePayoffs_tendsto (B : CountableInstance)
    (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal : ℝ)<bs m)
    (hNs : Tendsto Ns atTop atTop) (hbsLim : Tendsto bs atTop (𝓝 (B.terminal : ℝ)))
    (Z : CompleteWorld Unit → ℝ) (hZ : MemLp Z 2 (B.completeWorldLaw (Measure.dirac ()))) :
    Tendsto (fun m => ∫ v, Z v*(B.truncatedValueRule (Ns m) (bs m) (hbs m) w c).realizedReward B.terminal v
      ∂B.completeWorldLaw (Measure.dirac ())) atTop
      (𝓝 (∫ v, Z v*(B.valueRule w c).realizedReward B.terminal v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => ∫ v, Z v*(B.truncatedValueRule (Ns m) (bs m) (hbs m) w c).realizedDuration v
      ∂B.completeWorldLaw (Measure.dirac ())) atTop
      (𝓝 (∫ v, Z v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  let π := fun m => B.truncatedValuePolicy (Ns m) (bs m) (hbs m) hw.le hc.le
  let I := ∫ v, Z v^2 ∂B.completeWorldLaw (Measure.dirac ())
  have hError := B.truncatedValuePolicy_outcomeError_tendsto hZero hw hc Ns bs hbs hNs hbsLim
  have hLimit : Tendsto (fun m => Real.sqrt (2*I*((B.cap : ℝ)+1)*(π m).expectedValueOutcomeError w c))
      atTop (𝓝 (0 : ℝ)) := by
    have h0 : Tendsto (fun m => 2*I*((B.cap : ℝ)+1)*(π m).expectedValueOutcomeError w c) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hError.const_mul (2*I*((B.cap : ℝ)+1))
    simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h0
  have hBounds (m : ℕ) := (π m).score_stability hw.le hc.le Z hZ (le_refl I)
    (le_refl ((π m).expectedValueOutcomeError w c))
  have hBase := (B.valueRule w c).integrable_score_products (B.valueRule_isMeasurable hw.le hc.le) (Measure.dirac ()) hZ
  have hInt (m : ℕ) := (π m).rule.integrable_score_products (π m).measurable_rule (Measure.dirac ()) hZ
  have hRD (m : ℕ) : (∫ v, Z v*(π m).coupledRewardDifference w c v ∂B.completeWorldLaw (Measure.dirac ()))=
      (∫ v, Z v*(B.truncatedValueRule (Ns m) (bs m) (hbs m) w c).realizedReward B.terminal v ∂B.completeWorldLaw (Measure.dirac ()))-
        ∫ v, Z v*(B.valueRule w c).realizedReward B.terminal v ∂B.completeWorldLaw (Measure.dirac ()) := by
    simp only [RandomizedCountablePolicy.coupledRewardDifference,mul_sub]
    exact integral_sub (hInt m).1 hBase.1
  have hTD (m : ℕ) : (∫ v, Z v*(π m).coupledDurationDifference w c v ∂B.completeWorldLaw (Measure.dirac ()))=
      (∫ v, Z v*(B.truncatedValueRule (Ns m) (bs m) (hbs m) w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))-
        ∫ v, Z v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()) := by
    simp only [RandomizedCountablePolicy.coupledDurationDifference,mul_sub]
    exact integral_sub (hInt m).2 hBase.2
  constructor
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hLimit
    intro m
    rw [Real.norm_eq_abs,←hRD m]
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hBounds m)
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hLimit
    intro m
    rw [Real.norm_eq_abs,←hTD m]
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hBounds m)

end ProphetSecretary.Limiting
