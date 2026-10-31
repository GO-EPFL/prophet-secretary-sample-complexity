import ProphetSecretary.Limiting.CountablePoissonBands
import ProphetSecretary.Limiting.HybridMaximumDistribution

/-!
# Actual void probabilities above the reserve

Only finitely many construction bands can meet a fixed upper mark tail.
Independence of their actual configurations and finite Poisson void laws give
the exact exponential void probability for the countable configuration.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance)

lemma bandIntensity_tail_zero {b : ℝ} {K : ℕ}
    (hK : ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b) (k : ℕ) (hk : K < k) :
    (B.bandIntensity k : Measure ℝ) (Ioi b) = 0 := by
  change B.intensity.restrict (B.markBand k) (Ioi b) = 0
  rw [Measure.restrict_apply measurableSet_Ioi]
  have he : Ioi b ∩ B.markBand k = ∅ := by
    ext x
    simp only [mem_inter_iff,mem_Ioi,mem_empty_iff_false,iff_false,not_and]
    intro hx hm
    exact (not_lt_of_ge (hK k hk x hm)) hx
  rw [he,measure_empty]

lemma bandConfigurations_no_marks_above_probability {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    B.bandConfigurationsLaw {ω | ∀ k j, ((ω k).2 j).2 ≤ b} =
      ENNReal.ofReal (Real.exp (-B.intensity.real (Ioi b))) := by
  obtain ⟨K,hK⟩ := B.eventually_bands_below hb
  have htzero (k : ℕ) (hk : k ∉ Finset.range (K+1)) :
      (B.bandIntensity k : Measure ℝ) (Ioi b) = 0 :=
    B.bandIntensity_tail_zero hK k (by simp only [Finset.mem_range,not_lt] at hk; omega)
  have he : {ω : BandConfigurations | ∀ k j, ((ω k).2 j).2 ≤ b} =
      univ.pi (fun _ : ℕ => {ω : Configuration | ∀ j, (ω.2 j).2 ≤ b}) := by
    ext ω
    simp
  rw [he,bandConfigurationsLaw,Measure.infinitePi_pi_univ _ (fun _ => measurableSet_no_marks_above b)]
  simp_rw [configuration_no_marks_above_probability]
  have hprod : (∏' k, ENNReal.ofReal (Real.exp (-(B.bandIntensity k : Measure ℝ).real (Ioi b)))) =
      ∏ k ∈ Finset.range (K+1), ENNReal.ofReal (Real.exp (-(B.bandIntensity k : Measure ℝ).real (Ioi b))) := by
    apply tprod_eq_prod
    intro k hk
    rw [Measure.real,htzero k hk]
    simp
  rw [hprod,← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  have hsum : (∑ k ∈ Finset.range (K+1), (B.bandIntensity k : Measure ℝ).real (Ioi b)) = B.intensity.real (Ioi b) := by
    have he := congrArg (fun μ : Measure ℝ => μ (Ioi b)) B.sum_bandIntensity
    rw [Measure.sum_apply _ measurableSet_Ioi,tsum_eq_sum htzero] at he
    rw [Measure.real,← he,ENNReal.toReal_sum]
    · rfl
    · intro k _
      exact measure_ne_top _ _
  congr 1
  rw [← Real.exp_sum,Finset.sum_neg_distrib,hsum]

end ProphetSecretary.Limiting.CountableInstance
