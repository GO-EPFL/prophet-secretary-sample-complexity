import ProphetSecretary.Probability.FourthMoment

/-!
# Local empirical positive-part moment estimates

For a fixed measurable `f` with `0≤f≤1`, the variance and fourth moment of its centered
empirical mean are controlled by `P f`, with explicit constants independent of the
number of online identities. These are sampling statements, before any scalar selection.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics

variable {k : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma integral_pi_coordinate {f : ℝ → ℝ} (hfm : Measurable f) (j : Fin k) :
    (∫ v : Fin k → ℝ, f (v j) ∂Measure.pi (fun _ : Fin k => μ)) = ∫ x, f x ∂μ := by
  have hp := measurePreserving_eval (fun _ : Fin k => μ) j
  have h := integral_map (μ := Measure.pi (fun _ : Fin k => μ)) hp.measurable.aemeasurable hfm.aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h.symm

lemma bounded_centered_moments {f : ℝ → ℝ} (hfm : Measurable f)
    (hb : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) :
    let p := ∫ x, f x ∂μ
    0 ≤ p ∧ p ≤ 1 ∧
      (∀ᵐ x ∂μ, |f x - p| ≤ 1) ∧
      (∫ x, f x - p ∂μ) = 0 ∧
      (∫ x, (f x - p) ^ 2 ∂μ) ≤ p ∧
      (∫ x, (f x - p) ^ 4 ∂μ) ≤ p := by
  let p := ∫ x, f x ∂μ
  have hfi : Integrable f μ := by
    apply Integrable.of_bound hfm.aestronglyMeasurable 1
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hp0 : 0 ≤ p := integral_nonneg_of_ae (hb.mono fun _ h => h.1)
  have hp1 : p ≤ 1 := by
    have h := integral_mono_ae hfi (integrable_const (1 : ℝ)) (hb.mono fun _ h => h.2)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have habs : ∀ᵐ x ∂μ, |f x - p| ≤ 1 := by
    filter_upwards [hb] with x hx
    rw [abs_le]
    constructor <;> linarith
  have hcenter : (∫ x, f x - p ∂μ) = 0 := by
    rw [integral_sub hfi (integrable_const p), integral_const, probReal_univ, one_smul]
    exact sub_self p
  have hfi2 : Integrable (fun x => f x ^ 2) μ := by
    apply ProphetSecretary.Probability.integrable_pow_of_bound hfm zero_le_one _ 2
    exact hb.mono fun x hx => by simpa only [abs_of_nonneg hx.1] using hx.2
  have hI2 : Integrable (fun x => (f x - p) ^ 2) μ :=
    ProphetSecretary.Probability.integrable_pow_of_bound (hfm.sub measurable_const) zero_le_one habs 2
  have hI4 : Integrable (fun x => (f x - p) ^ 4) μ :=
    ProphetSecretary.Probability.integrable_pow_of_bound (hfm.sub measurable_const) zero_le_one habs 4
  have hexpand : (∫ x, (f x - p) ^ 2 ∂μ) = (∫ x, f x ^ 2 ∂μ) - p ^ 2 := by
    have he : (fun x => (f x - p) ^ 2) = (fun x => (f x ^ 2 - 2 * p * f x) + p ^ 2) := by
      funext x
      ring
    rw [he, integral_add (f := fun x => f x ^ 2 - 2 * p * f x) (g := fun _ => p ^ 2)
      (hfi2.sub (hfi.const_mul (2 * p))) (integrable_const _),
      integral_sub (f := fun x => f x ^ 2) (g := fun x => 2 * p * f x) hfi2 (hfi.const_mul (2 * p)), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    dsimp [p]
    ring
  have hf2 : (∫ x, f x ^ 2 ∂μ) ≤ p := by
    apply integral_mono_ae hfi2 hfi
    filter_upwards [hb] with x hx
    nlinarith
  have h2 : (∫ x, (f x - p) ^ 2 ∂μ) ≤ p := by rw [hexpand]; nlinarith [sq_nonneg p]
  have h4 : (∫ x, (f x - p) ^ 4 ∂μ) ≤ p := by
    apply (integral_mono_ae hI4 hI2 ?_).trans h2
    filter_upwards [habs] with x hx
    have hxx := abs_le.mp hx
    have hs : (f x - p) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg (f x - p)) (sub_nonneg.mpr hs)]
  exact ⟨hp0, hp1, habs, hcenter, h2, h4⟩

/-- The sixth conditional moment of one centered bounded sample is also at most
its uncentered mean. This controls the sixth powers of sample-by-sample martingale jumps. -/
lemma bounded_centered_sixthMoment_le_mean {f : ℝ → ℝ} (hfm : Measurable f)
    (hb : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) :
    (∫ x, (f x - ∫ z, f z ∂μ) ^ 6 ∂μ) ≤ ∫ x, f x ∂μ := by
  obtain ⟨_hp0, _hp1, habs, _hm, h2, _h4⟩ := bounded_centered_moments hfm hb
  have hI2 := ProphetSecretary.Probability.integrable_pow_of_bound (hfm.sub measurable_const) zero_le_one habs 2
  have hI6 := ProphetSecretary.Probability.integrable_pow_of_bound (hfm.sub measurable_const) zero_le_one habs 6
  apply (integral_mono_ae hI6 hI2 ?_).trans h2
  filter_upwards [habs] with x hx
  let d := f x - ∫ z, f z ∂μ
  change d ^ 6 ≤ d ^ 2
  calc
    d ^ 6 = |d| ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    _ ≤ |d| ^ 2 := pow_le_pow_of_le_one (abs_nonneg d) hx (by decide : 2 ≤ 6)
    _ = d ^ 2 := sq_abs d

/-- Localized second and fourth moments of the centered empirical mean. -/
theorem empirical_average_centered_moment_bounds [NeZero k] {f : ℝ → ℝ}
    (hfm : Measurable f) (hb : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) :
    let p := ∫ x, f x ∂μ
    let error := fun v : Fin k → ℝ => (k : ℝ)⁻¹ * ∑ j, (f (v j) - p)
    (∫ v, error v ^ 2 ∂Measure.pi (fun _ : Fin k => μ)) ≤ p / k ∧
    (∫ v, error v ^ 4 ∂Measure.pi (fun _ : Fin k => μ)) ≤
      p / (k : ℝ) ^ 3 + 3 * p ^ 2 / (k : ℝ) ^ 2 := by
  let p := ∫ x, f x ∂μ
  let X : Fin k → (Fin k → ℝ) → ℝ := fun j v => f (v j) - p
  obtain ⟨hp0, _hp1, habs, hm, h2, h4⟩ := bounded_centered_moments hfm hb
  have hX (j : Fin k) : Measurable (X j) := (hfm.comp (measurable_pi_apply j)).sub measurable_const
  have hInd : iIndepFun X (Measure.pi (fun _ : Fin k => μ)) :=
    iIndepFun_pi (fun _ => (hfm.sub measurable_const).aemeasurable)
  have hbound (j : Fin k) : ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ), |X j v| ≤ 1 :=
    (measurePreserving_eval (fun _ : Fin k => μ) j).quasiMeasurePreserving.ae habs
  have hmX (j : Fin k) : (∫ v, X j v ∂Measure.pi (fun _ : Fin k => μ)) = 0 :=
    (integral_pi_coordinate (hfm.sub measurable_const) j).trans hm
  have hX2 (j : Fin k) : (∫ v, X j v ^ 2 ∂Measure.pi (fun _ : Fin k => μ)) ≤ p :=
    (integral_pi_coordinate ((hfm.sub measurable_const).pow_const 2) j).trans_le h2
  have hX4 (j : Fin k) : (∫ v, X j v ^ 4 ∂Measure.pi (fun _ : Fin k => μ)) ≤ p :=
    (integral_pi_coordinate ((hfm.sub measurable_const).pow_const 4) j).trans_le h4
  have hsum := ProphetSecretary.Probability.centered_sum_moment_bounds Finset.univ X (fun _ => p)
    hX hInd hbound hmX (fun _ => hp0) hX2 hX4
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hsum
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  have he (a : ℕ) :
      (∫ v : Fin k → ℝ, ((k : ℝ)⁻¹ * ∑ j, X j v) ^ a ∂Measure.pi (fun _ : Fin k => μ)) =
        ((k : ℝ)⁻¹) ^ a * ∫ v, (∑ j, X j v) ^ a ∂Measure.pi (fun _ : Fin k => μ) := by
    simp only [mul_pow]
    exact integral_const_mul _ _
  constructor
  · rw [he 2]
    apply (mul_le_mul_of_nonneg_left hsum.1 (sq_nonneg _)).trans_eq
    change ((k : ℝ)⁻¹) ^ 2 * ((k : ℝ) * p) = p / (k : ℝ)
    field_simp
  · rw [he 4]
    apply (mul_le_mul_of_nonneg_left hsum.2 (by positivity)).trans_eq
    change ((k : ℝ)⁻¹) ^ 4 * ((k : ℝ) * p + 3 * ((k : ℝ) * p) ^ 2) =
      p / (k : ℝ) ^ 3 + 3 * p ^ 2 / (k : ℝ) ^ 2
    field_simp

end ProphetSecretary.Statistics
