import ProphetSecretary.Statistics.EmpiricalFreshStep

/-!
# Conditional moments for revealed bounded functions

A bounded function of the revealed reservoir and a fresh offer can be integrated
against the genuine fresh-coordinate law. Product independence is derived from
coordinate erasure. This also applies to normalized scalar premium increments.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Statistics

variable {Γ : Type*} [MeasurableSpace Γ]

noncomputable def centeredFreshStep (μ : Measure ℝ) (k : ℕ) (F : Γ × ℝ → ℝ) (v : Γ × ℝ) : ℝ :=
  (k : ℝ)⁻¹ * (F v - ∫ x, F (v.1, x) ∂μ)

lemma measurable_centeredFreshStep (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (k : ℕ) {F : Γ × ℝ → ℝ} (hF : Measurable F) : Measurable (centeredFreshStep μ k F) := by
  have hp : Measurable (fun a : Γ => ∫ x, F (a, x) ∂μ) := hF.stronglyMeasurable.integral_prod_right'.measurable
  exact (hF.sub (hp.comp measurable_fst)).const_mul _

lemma centeredFreshStep_moments (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (k : ℕ) {f : ℝ → ℝ} (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    let p := ∫ x, f x ∂μ
    let d := fun x => (k : ℝ)⁻¹ * (f x - p)
    (∀ x, |d x| ≤ (k : ℝ)⁻¹) ∧ (∫ x, d x ∂μ) = 0 ∧
      (∫ x, d x ^ 2 ∂μ) ≤ p / (k : ℝ) ^ 2 ∧
      (∫ x, d x ^ 6 ∂μ) ≤ p / (k : ℝ) ^ 6 := by
  obtain ⟨hp0, hp1, _habs, hm, h2, _h4⟩ := bounded_centered_moments (μ := μ) hf (Filter.Eventually.of_forall hb)
  have h6 := bounded_centered_sixthMoment_le_mean (μ := μ) hf (Filter.Eventually.of_forall hb)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    have hd : |f x - ∫ y, f y ∂μ| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [(hb x).1, (hb x).2]
    have hk : (0 : ℝ) ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg k)
    rw [abs_mul, abs_of_nonneg hk]
    exact (mul_le_mul_of_nonneg_left hd hk).trans_eq (mul_one _)
  · simp only [integral_const_mul, hm, mul_zero]
  · simp only [mul_pow, integral_const_mul]
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
      mul_le_mul_of_nonneg_left h2 (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)) 2)
  · simp only [mul_pow, integral_const_mul]
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
      mul_le_mul_of_nonneg_left h6 (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)) 6)

lemma integrable_centeredFreshStep_pow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ν : Measure Γ) [IsProbabilityMeasure ν] (k p : ℕ)
    {F : Γ × ℝ → ℝ} (hF : Measurable F) (hb : ∀ a x, 0 ≤ F (a, x) ∧ F (a, x) ≤ 1) :
    Integrable (fun v => centeredFreshStep μ k F v ^ p) (ν.prod μ) := by
  apply Integrable.of_bound ((measurable_centeredFreshStep μ k hF).pow_const p).aestronglyMeasurable (((k : ℝ)⁻¹) ^ p)
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_pow]
  apply pow_le_pow_left₀ (abs_nonneg _)
  exact (centeredFreshStep_moments μ k (hF.comp (measurable_const.prodMk measurable_id)) (hb v.1)).1 v.2

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model

variable {n k : ℕ}

/-- The actual fresh-coordinate conditional moment formula for any bounded
function invariant under the revealed-coordinate mask. -/
theorem Instance.boundedFreshStep_conditional_moments (P : Instance n)
    (q : Fin n × Fin k) (s : Finset (Fin n × Fin k)) (hq : q ∉ s)
    {F : (((Fin n × Fin k) → ℝ) × ℝ) → ℝ} (hF : Measurable F)
    (hb : ∀ a x, 0 ≤ F (a, x) ∧ F (a, x) ≤ 1)
    (hinv : ∀ a x, F (ProphetSecretary.Probability.maskCoordinates s a, x) = F (a, x)) :
    let ρ := P.trainingCoordinateLaw k
    let info := ProphetSecretary.Probability.revealedCoordinateSigma s
    let p := fun a => ∫ x, F (a, x) ∂P.law q.1
    let d := fun a => ProphetSecretary.Statistics.centeredFreshStep (P.law q.1) k F (a, a q)
    ρ[d | info] =ᵐ[ρ] 0 ∧
      (∀ᵐ a ∂ρ, (ρ[(fun a => d a ^ 2) | info]) a ≤ p a / (k : ℝ) ^ 2) ∧
      (∀ᵐ a ∂ρ, (ρ[(fun a => d a ^ 6) | info]) a ≤ p a / (k : ℝ) ^ 6) := by
  let ρ := P.trainingCoordinateLaw k
  let past := ρ.map (ProphetSecretary.Probability.maskCoordinates s)
  haveI : IsProbabilityMeasure past := Measure.isProbabilityMeasure_map
    (ProphetSecretary.Probability.measurable_maskCoordinates s).aemeasurable
  have hp : MeasurePreserving (fun a : (Fin n × Fin k) → ℝ =>
      (ProphetSecretary.Probability.maskCoordinates s a, a q)) ρ (past.prod (P.law q.1)) :=
    ProphetSecretary.Probability.revealedCoordinates_fresh_pair_measurePreserving (fun r : Fin n × Fin k => P.law r.1) hq
  have hCE (p : ℕ) : ρ[(fun a => ProphetSecretary.Statistics.centeredFreshStep (P.law q.1) k F (a, a q) ^ p) |
      ProphetSecretary.Probability.revealedCoordinateSigma s] =ᵐ[ρ]
      (fun a => ∫ x, ProphetSecretary.Statistics.centeredFreshStep (P.law q.1) k F (a, x) ^ p ∂P.law q.1) := by
    have h := ProphetSecretary.Probability.condExp_productPair past (P.law q.1) ρ hp
      (F := fun v => ProphetSecretary.Statistics.centeredFreshStep (P.law q.1) k F v ^ p)
      ((ProphetSecretary.Statistics.measurable_centeredFreshStep (P.law q.1) k hF).pow_const p)
      (ProphetSecretary.Statistics.integrable_centeredFreshStep_pow (P.law q.1) past k p hF hb)
    simpa only [ProphetSecretary.Statistics.centeredFreshStep, hinv] using h
  have hlocal (a : (Fin n × Fin k) → ℝ) := ProphetSecretary.Statistics.centeredFreshStep_moments
    (P.law q.1) k (hF.comp (measurable_const.prodMk measurable_id)) (hb a)
  refine ⟨?_, ?_, ?_⟩
  · have h := hCE 1
    simp only [pow_one] at h
    filter_upwards [h] with a ha
    exact ha.trans (hlocal a).2.1
  · filter_upwards [hCE 2] with a ha
    exact ha.trans_le (hlocal a).2.2.1
  · filter_upwards [hCE 6] with a ha
    exact ha.trans_le (hlocal a).2.2.2

end ProphetSecretary.Model
