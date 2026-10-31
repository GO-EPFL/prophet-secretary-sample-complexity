import ProphetSecretary.LowerBound.LikelihoodExperimentData
import ProphetSecretary.Stability.UniformResponseStability

/-!
# Bounded uniform response modulus for the actual likelihood experiment

The same modulus controls the sum of the actual A and B derivative changes
for every randomized competing policy. Its explicit bound and right limit
are independent of the array dimension. No total-first-moment hypothesis
or restricted policy class appears.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.LowerBound
open ProphetSecretary.Model ProphetSecretary.Probability

theorem likelihoodExperiment_response_stability
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H δ I : ℝ}
    (hH : 0≤H) (hδ : 0<δ) (hI : 0≤I)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (L : ℝ → ℝ) (hL : ∀ d, 0<d → 0≤L d) (hTail : ∀ m d, 0<d → (P m).tailCount d≤L d)
    (lams : ℕ → ℝ) (hRange : ∀ m, lams m∈Icc δ (1-δ))
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    let E := likelihoodExperiment sizes P score hh hb hm lams
    let πopt := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
      (hδ.le.trans (hRange m).1) (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])
    ∃ ω : ℝ → ℝ, Monotone ω ∧
      (∀ s, 0≤s → 0≤ω s ∧ ω s≤2*Real.sqrt (2*I*(H+1)*(H+1))) ∧ ω 0=0 ∧
      Tendsto ω (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) ∧
      ∀ m (π : RandomizedPolicy (sizes m)),
        |deriv (E.baseWeightGap m π) 0-deriv (E.baseWeightGap m (πopt m)) 0|+
          |deriv (E.balanceDifference m π) 0-deriv (E.balanceDifference m (πopt m)) 0|≤
            ω (E.scalarRegret m π) := by
  let E := likelihoodExperiment sizes P score hh hb hm lams
  let πopt := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
    (hδ.le.trans (hRange m).1) (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])
  obtain ⟨Ω,hΩ,hMono,hZero,hLim,hRoot,hResp⟩ := finite_uniform_response_stability sizes P hH hδ hI hCap L hL hTail
    lams hRange score hh hb hm hInfo
  let K := 2*I*(H+1)
  let ω := fun s => 2*Real.sqrt (K*Ω s)
  have hK : 0≤K := by dsimp [K];positivity
  have hωMono : Monotone ω := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hMono hab) hK)) (by norm_num)
  have hωBound (s : ℝ) (_hs : 0≤s) : 0≤ω s ∧ ω s≤2*Real.sqrt (2*I*(H+1)*(H+1)) := by
    exact ⟨by dsimp [ω];positivity,
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hΩ s).2 hK)) (by norm_num)⟩
  have hωZero : ω 0=0 := by simp only [ω,hZero,mul_zero,Real.sqrt_zero]
  have hωLim : Tendsto ω (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa only [ω,K,mul_zero] using hRoot.const_mul 2
  have hUnit (m) : lams m∈Icc (0:ℝ) 1 := ⟨hδ.le.trans (hRange m).1,by linarith only [(hRange m).2,hδ.le]⟩
  have hA (m) (π : RandomizedPolicy (sizes m)) : deriv (E.baseWeightGap m π) 0=
      π.normalizedScoreResponse (P m) (score m) (lams m) :=
    likelihoodExperiment_gap_deriv sizes P hH hCap score hh hb hm lams hUnit m π
  have hB (m) (π : RandomizedPolicy (sizes m)) : deriv (E.balanceDifference m π) 0=
      π.targetScoreResponse (P m) (score m) :=
    likelihoodExperiment_balance_deriv sizes P hH hCap score hh hb hm lams m π
  have hRegret (m) (π : RandomizedPolicy (sizes m)) : E.scalarRegret m π=
      optimalScalarValue (P m) (lams m) (1-lams m)-π.scalarObjective (P m) (lams m) (1-lams m) := by
    change optimalScalarValue ((P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) 0) (lams m) (1-lams m)-
      π.scalarObjective ((P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) 0) (lams m) (1-lams m)=_
    rw [(P m).likelihoodWidePath_zero_eq (score m) (hh m) (hb m) (hm m)]
  refine ⟨ω,hωMono,hωBound,hωZero,hωLim,?_⟩
  intro m π
  rw [hA m π,hA m (πopt m),hB m π,hB m (πopt m)]
  have h := hResp m π (E.scalarRegret m π) (le_of_eq (hRegret m π).symm)
  exact (add_le_add h.1 h.2).trans_eq (by dsimp only [ω,K];ring)
end ProphetSecretary.LowerBound
