import ProphetSecretary.Probability.ScorePayoffComparison

/-!
# Small square-integrable errors against bounded payoffs

Only an almost-sure payoff bound is required. No independence between the
analytical score error and the payoff is assumed. These estimates transfer
joint expectations from zero-atom likelihood scores to literal centered
finite point counts in `lem:coarse-policy`.
-/

open MeasureTheory Filter
open scoped Topology ENNReal
namespace ProphetSecretary.Probability

lemma boundedPayoff_integrable_and_integral_le_L2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E G : Ω → ℝ)
    (hE : MemLp E 2 μ) (hG : AEStronglyMeasurable G μ) {D : ℝ}
    (hD : 0≤D) (hBound : ∀ᵐ v ∂μ, |G v|≤D) :
    Integrable (fun v => E v*G v) μ ∧
      |∫ v, E v*G v ∂μ|≤D*Real.sqrt (∫ v, (E v)^2 ∂μ) := by
  have h := bounded_score_payoff_memLp_and_secondMoment μ E G hE hG (le_refl _) hD hBound
  refine ⟨h.1.integrable (by norm_num : (1:ℝ≥0∞)≤2),?_⟩
  have hMean := abs_integral_le_sqrt_secondMoment μ _ h.1 h.2
  simpa only [Real.sqrt_mul (sq_nonneg D),Real.sqrt_sq hD] using hMean

lemma boundedPayoff_integral_le_of_integrable_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E G : Ω → ℝ)
    (hE : Measurable E) (hG : Measurable G) (hSquare : Integrable (fun v => (E v)^2) μ)
    {D : ℝ} (hD : 0≤D) (hBound : ∀ᵐ v ∂μ, |G v|≤D) :
    Integrable (fun v => E v*G v) μ ∧
      |∫ v, E v*G v ∂μ|≤D*Real.sqrt (∫ v, (E v)^2 ∂μ) :=
  boundedPayoff_integrable_and_integral_le_L2 μ E G
    ((memLp_two_iff_integrable_sq hE.aestronglyMeasurable).mpr hSquare)
    hG.aestronglyMeasurable hD hBound

lemma score_payoff_difference_le_L2_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s t G : Ω → ℝ)
    (hs : MemLp s 2 μ) (ht : MemLp t 2 μ) (hG : AEStronglyMeasurable G μ)
    {D I : ℝ} (hD : 0≤D) (hBound : ∀ᵐ v ∂μ, |G v|≤D)
    (hError : (∫ v, (s v-t v)^2 ∂μ)≤I) :
    |(∫ v, s v*G v ∂μ)-(∫ v, t v*G v ∂μ)|≤D*Real.sqrt I := by
  have hsInt := (boundedPayoff_integrable_and_integral_le_L2 μ s G hs hG hD hBound).1
  have htInt := (boundedPayoff_integrable_and_integral_le_L2 μ t G ht hG hD hBound).1
  rw [←integral_sub hsInt htInt]
  have hFunctions : (fun v => s v*G v-t v*G v)=(fun v => (s v-t v)*G v) :=
    funext (fun v => (sub_mul (s v) (t v) (G v)).symm)
  rw [hFunctions]
  exact (boundedPayoff_integrable_and_integral_le_L2 μ (fun v => s v-t v) G
    (hs.sub ht) hG hD hBound).2.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hError) hD)

theorem integral_boundedPayoff_tendsto_zero_of_L2 (Ω : ℕ → Type*)
    [∀ m, MeasurableSpace (Ω m)] (μ : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    (E G : ∀ m, Ω m → ℝ) (hE : ∀ m, MemLp (E m) 2 (μ m))
    (hG : ∀ m, AEStronglyMeasurable (G m) (μ m)) {D : ℝ} (hD : 0≤D)
    (hBound : ∀ m, ∀ᵐ v ∂μ m, |G m v|≤D)
    (hError : Tendsto (fun m => ∫ v, (E m v)^2 ∂μ m) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun m => ∫ v, E m v*G m v ∂μ m) atTop (𝓝 (0:ℝ)) := by
  have hUpper : Tendsto (fun m => D*Real.sqrt (∫ v, (E m v)^2 ∂μ m)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_apply,Real.sqrt_zero,mul_zero] using
      ((Real.continuous_sqrt.tendsto 0).comp hError).const_mul D
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun m => by simpa only [Real.norm_eq_abs] using
      (boundedPayoff_integrable_and_integral_le_L2 (μ m) (E m) (G m) (hE m) (hG m) hD (hBound m)).2) hUpper

end ProphetSecretary.Probability
