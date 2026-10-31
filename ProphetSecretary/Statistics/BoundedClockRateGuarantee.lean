import ProphetSecretary.Statistics.BoundedClockMeshLearner
import ProphetSecretary.Analysis.MeshDeficitAbsorption

/-!
# Explicit competitive constants after the probability-grid transfer

The numerical rate lower bound is a hypothesis here; its statistical proof
is separate. Once it holds, the concrete fixed clock learner has both
reward and reach guarantees with the same constant A+1/μ+1, independent
of the number of variables and finite alphabet size.
-/

open MeasureTheory Set
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Analysis

noncomputable def boundedResponseConstant (A μ : ℝ) : ℝ := A+1/μ+1

lemma boundedResponseConstant_positive {A μ : ℝ} (hA : 0≤A) (hμ : 0<μ) :
    0<boundedResponseConstant A μ := by unfold boundedResponseConstant; positivity

theorem boundedClockMeshLearner_guarantees_of_rate {n k m : ℕ} (G : Finset ℝ)
    (hBound : ∀ x∈G, x∈Icc (0 : ℝ) 1) (hz : (0 : ℝ)∈G)
    (hm : 0<m) {μ : ℝ} (hμ : 0<μ) (μhi ℓ : ℝ) {A C : ℝ}
    (hRate : C-A/(m : ℝ)≤boundedMeshRate n k m G (fun x hx => (hBound x hx).1) μ μhi ℓ)
    (P : Instance n) (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G)
    (hMean : μ≤P.expectedMaximum) (hUpper : P.expectedMaximum≤μhi) (hCount : P.positiveCount≤ℓ) :
    (C-boundedResponseConstant A μ/(m : ℝ))*P.expectedMaximum≤
      (boundedClockMeshLearner (n:=n) (k:=k) m G (fun x hx => (hBound x hx).1) μ μhi ℓ).expectedReward P ∧
    ∀ i, C-boundedResponseConstant A μ/(m : ℝ)≤
      (boundedClockMeshLearner (n:=n) (k:=k) m G (fun x hx => (hBound x hx).1) μ μhi ℓ).reachProbability P i := by
  have hmOne : (1 : ℝ)≤m := by exact_mod_cast hm
  have hmNonneg : (0 : ℝ)≤m := by positivity
  have h := boundedClockMeshLearner_guarantees_at_rate (k:=k) G hBound hz hm hμ μhi ℓ P hG hMean hUpper hCount
  constructor
  · have hReward := mesh_reward_deficit_absorption hmOne hμ hMean hRate h.1
    have hCoeff : C-boundedResponseConstant A μ/(m : ℝ)≤C-(A+1/μ)/(m : ℝ) := by
      apply sub_le_sub_left
      apply div_le_div_of_nonneg_right _ hmNonneg
      unfold boundedResponseConstant
      linarith
    exact (mul_le_mul_of_nonneg_right hCoeff (hμ.le.trans hMean)).trans hReward
  · intro i
    have hReach := mesh_reach_deficit_absorption hmOne hRate (h.2 i)
    have hCoeff : C-boundedResponseConstant A μ/(m : ℝ)≤C-(A+1)/(m : ℝ) := by
      apply sub_le_sub_left
      apply div_le_div_of_nonneg_right _ hmNonneg
      unfold boundedResponseConstant
      have hInv : 0≤1/μ := le_of_lt (one_div_pos.mpr hμ)
      linarith only [hInv]
    exact hCoeff.trans hReach

end ProphetSecretary.Statistics
