import ProphetSecretary.LowerBound.BayesianExperiment
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# From a finite Bayesian experiment to an inverse-linear sample bound

This is `thm:bayes`. The perturbation family and its uniform information, Taylor,
response-stability, and negative-response properties are hypotheses, exactly as
in the manuscript. Constructing such a family remains a separate dependency of
the unconditional sample lower bound. Constants are chosen before ε, the budget,
and the family of learners. The hard budget is uniform over every instance size.
-/

open MeasureTheory InformationTheory Set Filter
open ProphetSecretary.Model
open scoped Topology ENNReal

namespace ProphetSecretary.LowerBound.Experiment

lemma exists_zero_padding_error {e : ℝ} (he : 0 < e) :
    ∃ N : ℕ, 0 < N ∧ 20 / Real.sqrt (N : ℝ) ≤ e := by
  let q := 20 / e
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (1 + q ^ 2)
  have hNpos : 0 < (N : ℝ) := by nlinarith [sq_nonneg q]
  have hroot : q ≤ Real.sqrt (N : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N), Real.sqrt_nonneg (N : ℝ)]
  have hsqrt : 0 < Real.sqrt (N : ℝ) := hq.trans_le hroot
  refine ⟨N, Nat.cast_pos.mp hNpos, (div_le_iff₀ hsqrt).mpr ?_⟩
  have h := mul_le_mul_of_nonneg_left hroot he.le
  have heq : e * q = 20 := by dsimp [q]; field_simp
  rwa [heq] at h

lemma exists_modulus_error_radius (ω : ℝ → ℝ) {a B e : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (he : 0 < e) (hmono : Monotone ω)
    (hlim : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    ∃ τ, 0 < τ ∧ ∀ t, 0 ≤ t → t ≤ τ →
      ProphetSecretary.Statistics.bayesModulusError ω a B t ≤ e * t := by
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨s, hs, hsω⟩ := (hpos.and (Metric.tendsto_nhds.mp hlim (e / a) (div_pos he ha))).exists
  let τ := s / (2 * a * B + 1)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  refine ⟨τ, hτ, ?_⟩
  intro t ht htτ
  have hcross := (le_div_iff₀ (by positivity : 0 < 2 * a * B + 1)).mp htτ
  have hlevel : 2 * a * B * t ≤ s := by nlinarith
  have hsbound : ω s ≤ e / a := by
    rw [Real.dist_eq, sub_zero] at hsω
    exact (le_abs_self _).trans hsω.le
  have hω := (hmono hlevel).trans hsbound
  have hm := mul_le_mul_of_nonneg_left hω (mul_nonneg ha.le ht)
  have heq : a * t * (e / a) = e * t := by field_simp [ha.ne']
  simpa only [ProphetSecretary.Statistics.bayesModulusError, heq] using hm

/-- `thm:bayes`, with explicit constants and uniform quantifiers. The normalized
base benchmark is retained as a manuscript premise; the statistical reduction
itself uses the stated critical gaps. -/
theorem bayes_sample_lower_bound (E : Experiment)
    (πopt : ∀ m, RandomizedPolicy (E.size m))
    {α H I b C ρ B : ℝ} (hα : 0 < α) (_hαhalf : α < 1 / 2)
    (hH : 0 ≤ H) (hI : 0 < I) (hb : 0 < b) (hC : 0 ≤ C) (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hweight : ∀ m, E.weight m ∈ Icc α (1 - α))
    (hbound : ∀ m θ, |θ| ≤ ρ → ∀ i, ∀ᵐ x ∂(E.law m θ).law i, x ≤ H)
    (_hNormalized : ∀ m, (E.law m 0).expectedMaximum = 1)
    (hopt : ∀ m, (πopt m).scalarObjective (E.law m 0) (E.weight m) (1 - E.weight m) =
      optimalScalarValue (E.law m 0) (E.weight m) (1 - E.weight m))
    (hcritical : Tendsto (fun m => E.baseWeightGap m (πopt m) 0) atTop (𝓝 (0 : ℝ)))
    (ω : ℝ → ℝ) (hmono : Monotone ω) (hω : ∀ s, 0 ≤ s → 0 ≤ ω s ∧ ω s ≤ B)
    (_hωzero : ω 0 = 0) (hωlim : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hInformation : ∀ (m k : ℕ) (L : Learner (E.size m) k) (t : ℝ), 0 < t → t ≤ ρ →
      klDiv (L.transcriptLaw (E.law m t)) (L.transcriptLaw (E.law m (-t))) +
      klDiv (L.transcriptLaw (E.law m (-t))) (L.transcriptLaw (E.law m t)) ≤
        ENNReal.ofReal (I * (k : ℝ) * t ^ 2))
    (hTaylor : ∀ (m : ℕ) (π : RandomizedPolicy (E.size m)) (θ : ℝ), |θ| ≤ ρ →
      (|E.baseWeightGap m π θ - E.baseWeightGap m π 0 - θ * deriv (E.baseWeightGap m π) 0| ≤ C * θ ^ 2) ∧
      (|E.balanceDifference m π θ - E.balanceDifference m π 0 - θ * deriv (E.balanceDifference m π) 0| ≤ C * θ ^ 2))
    (hResponse : ∀ (m : ℕ) (π : RandomizedPolicy (E.size m)),
      |deriv (E.baseWeightGap m π) 0 - deriv (E.baseWeightGap m (πopt m)) 0| +
      |deriv (E.balanceDifference m π) 0 - deriv (E.balanceDifference m (πopt m)) 0| ≤ ω (E.scalarRegret m π))
    (hNegative : ∀ m, deriv (E.balanceDifference m (πopt m)) 0 ≤ -b) :
    ∃ a ε₀ : ℝ, 0 < a ∧ 0 < ε₀ ∧ ∀ ε, ε ∈ Ioo (0 : ℝ) ε₀ →
      ∀ k : ℕ, FeasibleBudget ε k → a / ε ≤ (k : ℝ) := by
  let v := α / 2
  have hv : 0 < v := by dsimp [v]; positivity
  let d := v * b
  have hd : 0 < d := mul_pos hv hb
  let K := scalarSlopeConstant α (1 - α) H
  let A := ((K * v) ^ 2 / 8) * I
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let a₀ := d / (8 * (A + 1))
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  have hAa₀ : A * a₀ ≤ d / 8 := by
    calc
      _ ≤ (A + 1) * a₀ := mul_le_mul_of_nonneg_right (by linarith) ha₀.le
      _ = d / 8 := by dsimp [a₀]; field_simp
  let L := 8 * (H + 1) / d
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨τ, hτ, hmod⟩ := exists_modulus_error_radius ω (a := 1 + v) (B := B)
    (by linarith : 0 < 1 + v) hB (by positivity : 0 < d / 8) hmono hωlim
  let τTaylor := d / (8 * (1 + v) * (C + 1))
  have hτTaylor : 0 < τTaylor := by dsimp [τTaylor]; positivity
  let radius := min ρ (min τ τTaylor)
  have hradius : 0 < radius := lt_min hρ (lt_min hτ hτTaylor)
  let ε₀ := radius / L
  let a := a₀ / L
  refine ⟨a, ε₀, div_pos ha₀ hL, div_pos hradius hL, ?_⟩
  intro ε hε k hfeasible
  by_contra hk
  have hεpos : 0 < ε := hε.1
  have hksmall : (k : ℝ) * ε < a := (lt_div_iff₀ hεpos).mp (not_le.mp hk)
  let t := L * ε
  have ht : 0 < t := mul_pos hL hεpos
  have htradius : t < radius := by
    have h := (lt_div_iff₀ hL).mp hε.2
    simpa only [t, mul_comm] using h
  have htρ : t ≤ ρ := htradius.le.trans (min_le_left _ _)
  have htτ : t ≤ τ := htradius.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htTaylor : t ≤ τTaylor := htradius.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hkt : (k : ℝ) * t ≤ a₀ := by
    have h := mul_lt_mul_of_pos_left hksmall hL
    have heq : L * a = a₀ := by dsimp [a]; field_simp
    rw [heq] at h
    dsimp [t]
    nlinarith only [h]
  have hsample : A * (k : ℝ) * t ^ 2 ≤ d * t / 8 := by
    have h₁ := (mul_le_mul_of_nonneg_left hkt hA).trans hAa₀
    have h₂ := mul_le_mul_of_nonneg_right h₁ ht.le
    nlinarith only [h₂]
  have hmodulus : ProphetSecretary.Statistics.bayesModulusError ω (1 + v) B t ≤ d * t / 8 := by
    have h := hmod t ht.le htτ
    nlinarith only [h]
  have hTaylorError : (1 + v) * C * t ^ 2 ≤ d * t / 8 := by
    have hcross := (le_div_iff₀ (by positivity : 0 < 8 * (1 + v) * (C + 1))).mp htTaylor
    have hcoef : (1 + v) * C * t ≤ d / 8 := by
      have hpos := mul_nonneg (by linarith : 0 ≤ 1 + v) ht.le
      nlinarith only [hcross, hpos]
    have hm := mul_le_mul_of_nonneg_right hcoef ht.le
    nlinarith only [hm]
  obtain ⟨m, hm⟩ := (Metric.tendsto_nhds.mp hcritical (d * t / 8) (by positivity)).exists
  have hcritical_m : E.baseWeightGap m (πopt m) 0 ≤ d * t / 8 := by
    rw [Real.dist_eq, sub_zero] at hm
    exact (le_abs_self _).trans hm.le
  obtain ⟨N, hN, hNerror⟩ := exists_zero_padding_error (by positivity : 0 < d * t / 8)
  obtain ⟨learners, hGuarantee⟩ := hfeasible
  let learner := learners (E.size m + N)
  let baseLearner := learner.removeZeros
  have hboundBase := hbound m 0 (by simpa only [abs_zero] using hρ.le)
  have hboundPlus := hbound m t (by rwa [abs_of_pos ht])
  have hboundMinus := hbound m (-t) (by simpa only [abs_neg, abs_of_pos ht] using htρ)
  have hTay : ∀ π : RandomizedPolicy (E.size m),
      (|E.baseWeightGap m π t - E.baseWeightGap m π 0 - t * deriv (E.baseWeightGap m π) 0| ≤ C * t ^ 2) ∧
      (|E.baseWeightGap m π (-t) - E.baseWeightGap m π 0 + t * deriv (E.baseWeightGap m π) 0| ≤ C * t ^ 2) ∧
      (|E.balanceDifference m π t - E.balanceDifference m π 0 - t * deriv (E.balanceDifference m π) 0| ≤ C * t ^ 2) ∧
      (|E.balanceDifference m π (-t) - E.balanceDifference m π 0 + t * deriv (E.balanceDifference m π) 0| ≤ C * t ^ 2) := by
    intro π
    have hp := hTaylor m π t (by rwa [abs_of_pos ht])
    have hn := hTaylor m π (-t) (by simpa only [abs_neg, abs_of_pos ht] using htρ)
    refine ⟨hp.1, ?_, hp.2, ?_⟩
    · simpa only [neg_mul, sub_neg_eq_add, neg_sq] using hn.1
    · simpa only [neg_mul, sub_neg_eq_add, neg_sq] using hn.2
  have hUpper := E.binary_experiment_upper m baseLearner (πopt m) hα hH hv.le ht.le hI.le
    (hweight m) hboundBase ((E.law m t).integrable_maximum_of_bounded hboundPlus)
    ((E.law m (-t)).integrable_maximum_of_bounded hboundMinus) (hopt m) ω hB hmono hω
    (hInformation m k baseLearner.fullSampling t ht htρ) hTay (hResponse m) (hNegative m)
  have hUpper' : (1 / 2 : ℝ) * E.trainedTargetGap m baseLearner t v +
      (1 / 2 : ℝ) * E.trainedTargetGap m baseLearner (-t) (-v) ≤
      E.baseWeightGap m (πopt m) 0 - d * t + A * (k : ℝ) * t ^ 2 +
        ProphetSecretary.Statistics.bayesModulusError ω (1 + v) B t + (1 + v) * C * t ^ 2 := by
    convert hUpper using 1
    dsimp [d, A, K]
    ring
  have hUpperFinal : (1 / 2 : ℝ) * E.trainedTargetGap m baseLearner t v +
      (1 / 2 : ℝ) * E.trainedTargetGap m baseLearner (-t) (-v) ≤ -d * t / 2 := by
    linarith only [hUpper', hcritical_m, hsample, hmodulus, hTaylorError]
  have hw := hweight m
  have hLowerPlus := E.removedZeros_trainedTargetGap_ge m learner
    (hGuarantee (E.size m + N)) hεpos.le hH t v hboundPlus hN
    (by dsimp [v]; linarith [hw.1]) (by dsimp [v]; linarith [hw.2])
  have hLowerMinus := E.removedZeros_trainedTargetGap_ge m learner
    (hGuarantee (E.size m + N)) hεpos.le hH (-t) (-v) hboundMinus hN
    (by dsimp [v]; linarith [hw.1]) (by dsimp [v]; linarith [hw.2])
  have hεError : ε * (H + 1) = d * t / 8 := by dsimp [t, L]; field_simp
  change -ε * (H + 1) - 20 / Real.sqrt (N : ℝ) ≤ E.trainedTargetGap m baseLearner t v at hLowerPlus
  change -ε * (H + 1) - 20 / Real.sqrt (N : ℝ) ≤ E.trainedTargetGap m baseLearner (-t) (-v) at hLowerMinus
  have hpositive := mul_pos hd ht
  nlinarith only [hUpperFinal, hLowerPlus, hLowerMinus, hNerror, hεError, hpositive]

end ProphetSecretary.LowerBound.Experiment
