import ProphetSecretary.Stability.UniformScoreStability
import ProphetSecretary.Probability.TargetScoreResponse

/-!
# Uniform stability of the actual two likelihood derivatives

The normalized scalar-gap derivative and reward-minus-duration target
derivative are fixed-policy score expectations. The benchmark terms cancel
when policies are compared. Their common modulus is uniform over the array
index and every admissible randomized competing policy.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability

theorem finite_uniform_response_stability
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
        |π.normalizedScoreResponse (P m) (score m) (lams m)-ρ.normalizedScoreResponse (P m) (score m) (lams m)|≤
          Real.sqrt (2*I*(H+1)*Ω r) ∧
        |π.targetScoreResponse (P m) (score m)-ρ.targetScoreResponse (P m) (score m)|≤
          Real.sqrt (2*I*(H+1)*Ω r) := by
  obtain ⟨Ω,hΩ,hMono,hZero,hLim,hRoot,hScore⟩ := finite_uniform_score_stability sizes P hH hδ hI hCap L hL hTail
    lams hRange score hh hb hm hInfo
  refine ⟨Ω,hΩ,hMono,hZero,hLim,hRoot,?_⟩
  intro m π r hr
  let ρ := (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
    (hδ.le.trans (hRange m).1) (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])
  have hUnit : lams m∈Icc (0:ℝ) 1 := ⟨hδ.le.trans (hRange m).1,by linarith only [(hRange m).2,hδ.le]⟩
  have hPair := π.score_response_differences_le ρ (P m) (score m) hUnit
  exact ⟨hPair.1.trans (hScore m π r hr),hPair.2.trans (hScore m π r hr)⟩
end ProphetSecretary.Model
