import ProphetSecretary.Limiting.HybridScalarObjectives

/-!
# Changing only a finite-hybrid terminal reward

The full policy class and its observed histories are common to both states.
The terminal difference affects only no-selection executions, so the bound is
independent of the duration weight and retained dimension.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*}

lemma HybridRule.reward_terminal_le (π : HybridRule n Seed) (a b : ℝ) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) :
    π.reward a r x u ω ≤ π.reward b r x u ω+|a-b| := by
  unfold HybridRule.reward
  split_ifs
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · linarith only [le_abs_self (a-b)]

lemma RandomizedHybridPolicy.scalarObjective_terminal_le (π : RandomizedHybridPolicy n)
    (B D : FiniteIntensityHybridInstance n) (hP : D.individuals = B.individuals)
    (hμ : D.intensity = B.intensity) {w : ℝ} (hw : 0 ≤ w) (c : ℝ) :
    π.scalarObjective B w c ≤ π.scalarObjective D w c+w*|(B.terminal : ℝ)-D.terminal| := by
  have hlaw : D.law π.seedLaw = B.law π.seedLaw := by
    change hybridWorldLaw D.individuals D.intensity π.seedLaw = _
    rw [hP,hμ]
    rfl
  have hDI : Integrable (π.rule.realizedReward D.terminal) (B.law π.seedLaw) := hlaw ▸ π.integrable_reward D
  have hT := π.integrable_duration B
  have hJ : Integrable (fun v : HybridWorld n π.Seed =>
      w*π.rule.realizedReward D.terminal v+c*π.rule.realizedDuration v) (B.law π.seedLaw) :=
    (hDI.const_mul w).add (hT.const_mul c)
  have h := integral_mono (((π.integrable_reward B).const_mul w).add (hT.const_mul c))
    (hJ.add (integrable_const (w*|(B.terminal : ℝ)-D.terminal|))) (fun v => by
      have he := mul_le_mul_of_nonneg_left
        (π.rule.reward_terminal_le B.terminal D.terminal v.2.2.2 v.2.1 v.2.2.1 v.1) hw
      change w*π.rule.realizedReward B.terminal v+c*π.rule.realizedDuration v ≤
        (w*π.rule.realizedReward D.terminal v+c*π.rule.realizedDuration v)+w*|(B.terminal : ℝ)-D.terminal|
      change w*π.rule.realizedReward B.terminal v ≤
        w*(π.rule.realizedReward D.terminal v+|(B.terminal : ℝ)-D.terminal|) at he
      nlinarith only [he])
  change π.scalarObjective B w c ≤ ∫ v : HybridWorld n π.Seed,
    (w*π.rule.realizedReward D.terminal v+c*π.rule.realizedDuration v)+w*|(B.terminal : ℝ)-D.terminal|
      ∂B.law π.seedLaw at h
  rw [integral_add hJ (integrable_const _),integral_const,← hlaw] at h
  have he : (∫ v : HybridWorld n π.Seed, w*π.rule.realizedReward D.terminal v+c*π.rule.realizedDuration v ∂D.law π.seedLaw) =
      π.scalarObjective D w c := rfl
  rw [he] at h
  simpa only [probReal_univ,one_smul] using h

theorem FiniteIntensityHybridInstance.value_terminal_abs_sub_le
    (B D : FiniteIntensityHybridInstance n) (hP : D.individuals = B.individuals)
    (hμ : D.intensity = B.intensity) {w : ℝ} (hw : 0 ≤ w) (c : ℝ) :
    |B.optimalScalarValue w c-D.optimalScalarValue w c| ≤ w*|(B.terminal : ℝ)-D.terminal| := by
  have hBD : B.optimalScalarValue w c ≤ D.optimalScalarValue w c+w*|(B.terminal : ℝ)-D.terminal| := by
    apply csSup_le (B.scalarPayoffs_nonempty w c)
    rintro z ⟨π,rfl⟩
    exact (π.scalarObjective_terminal_le B D hP hμ hw c).trans
      (add_le_add (D.scalarObjective_le_value π w c) le_rfl)
  have hDB : D.optimalScalarValue w c ≤ B.optimalScalarValue w c+w*|(B.terminal : ℝ)-D.terminal| := by
    apply csSup_le (D.scalarPayoffs_nonempty w c)
    rintro z ⟨π,rfl⟩
    have h := (π.scalarObjective_terminal_le D B hP.symm hμ.symm hw c).trans
      (add_le_add (B.scalarObjective_le_value π w c) le_rfl)
    simpa only [abs_sub_comm] using h
  exact abs_sub_le_iff.mpr ⟨by linarith only [hBD],by linarith only [hDB]⟩

end ProphetSecretary.Limiting
