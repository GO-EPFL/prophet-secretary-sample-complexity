import ProphetSecretary.Stability.OutcomeStability
import ProphetSecretary.Stability.ExpectedScoreStability

/-!
# Uniform derivative-score stability under a common positive-tail profile

The modulus is chosen before the array index and the competing randomized
policy. It depends on the cap, interior weight margin, tail profile and the
uniform information bound, without a total-first-moment assumption. Complete
scores can include offers after stopping only as analytical multipliers.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability

theorem finite_uniform_score_stability
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H δ I : ℝ}
    (hH : 0≤H) (hδ : 0<δ) (hI : 0≤I)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (L : ℝ → ℝ) (hL : ∀ d, 0<d → 0≤L d) (hTail : ∀ m d, 0<d → (P m).tailCount d≤L d)
    (lams : ℕ → ℝ) (hRange : ∀ m, lams m∈Icc δ (1-δ))
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    ∃ Ω : ℝ → ℝ, (∀ r, 0≤Ω r ∧ Ω r≤H+1) ∧ Monotone Ω ∧ Ω 0=0 ∧
      Tendsto Ω (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) ∧
      Tendsto (fun r => Real.sqrt (2*I*(H+1)*Ω r)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) ∧
      ∀ m (π : RandomizedPolicy (sizes m)) (r : ℝ),
        optimalScalarValue (P m) (lams m) (1-lams m)-π.scalarObjective (P m) (lams m) (1-lams m)≤r →
        let ρ := (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
          (hδ.le.trans (hRange m).1) (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])
        |π.expectedRewardScore (P m) (score m)-ρ.expectedRewardScore (P m) (score m)|+
          |π.expectedDurationScore (P m) (score m)-ρ.expectedDurationScore (P m) (score m)|≤
            Real.sqrt (2*I*(H+1)*Ω r) := by
  obtain ⟨Ω,hΩ,hMono,hZero,hLim,hError,_hNeg⟩ := finite_outcome_stability_with_profile sizes P hH hδ hCap L hL hTail
  have hRoot : Tendsto (fun r => Real.sqrt (2*I*(H+1)*Ω r)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    have hMul : Tendsto (fun r => 2*I*(H+1)*Ω r) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa only [mul_zero] using hLim.const_mul (2*I*(H+1))
    simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hMul
  refine ⟨Ω,hΩ,hMono,hZero,hLim,hRoot,?_⟩
  intro m π r hr
  have hw : 0<lams m := hδ.trans_le (hRange m).1
  have hc : 0≤1-lams m := by linarith only [(hRange m).2,hδ.le]
  have hBase := π.expectedScore_stability (P m) hH (hCap m) hw hc (score m) (hh m) (hb m) (hm m) (hInfo m)
    (hError m (lams m) (1-lams m) (hRange m).1 (by linarith only [(hRange m).2]) (by ring) π)
  exact hBase.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hMono hr) (by positivity)))
end ProphetSecretary.Model
