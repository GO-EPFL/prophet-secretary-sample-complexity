import ProphetSecretary.Stability.OutcomeStability
import ProphetSecretary.Model.BellmanOptimal

/-!
# Likelihood scores and coupled outcomes

This instantiates `cor:score-stability` for the actual canonical optimizer and any
admissible competing policy. A score may use the complete offer vector, including
offers arriving after stopping. It is only an analytical variable.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def RandomizedPolicy.coupledRewardDifference (π : RandomizedPolicy n)
    (P : Instance n) (w c : ℝ) (ω : π.World) : ℝ :=
  π.realizedReward ω - (P.canonicalRule w c).reward () Finset.univ ω.1 ω.2.1

noncomputable def RandomizedPolicy.coupledDurationDifference (π : RandomizedPolicy n)
    (P : Instance n) (w c : ℝ) (ω : π.World) : ℝ :=
  π.realizedDuration ω - (P.canonicalRule w c).stoppingTime () Finset.univ ω.1 ω.2.1

lemma RandomizedPolicy.measurable_coupledDifferences (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Measurable (π.coupledRewardDifference P w c) ∧
      Measurable (π.coupledDurationDifference P w c) := by
  let ρ := P.canonicalRule w c
  have hρ : ρ.IsMeasurable := P.valueThreshold_policy_isMeasurable hP hw.le hc
  have hx (i : Fin n) : Measurable (fun ω : π.World => ω.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hu (i : Fin n) : Measurable (fun ω : π.World => ω.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  exact ⟨π.measurable_realizedReward.sub (ρ.measurable_reward hρ measurable_const hx hu Finset.univ),
    π.measurable_realizedDuration.sub (ρ.measurable_stoppingTime hρ measurable_const hx hu Finset.univ)⟩

lemma RandomizedPolicy.coupledDifferences_bounded (π : RandomizedPolicy n) (P : Instance n)
    {H w c : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    (∀ᵐ ω ∂P.worldLaw π.seedLaw, |π.coupledRewardDifference P w c ω| ≤ H) ∧
      (∀ᵐ ω ∂P.worldLaw π.seedLaw, |π.coupledDurationDifference P w c ω| ≤ 1) := by
  have hv : MeasurePreserving (fun ω : π.World => ω.1)
      (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  have hvalsH : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ H := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hbound i)
  have hboth : ∀ᵐ ω : π.World ∂P.worldLaw π.seedLaw,
      |π.coupledRewardDifference P w c ω| ≤ H ∧
        |π.coupledDurationDifference P w c ω| ≤ 1 := by
    filter_upwards [hv.quasiMeasurePreserving.ae P.ae_nonnegative,
      hv.quasiMeasurePreserving.ae hvalsH,
      P.world_clocks_mem_unitInterval π.seedLaw] with ω hx0 hxH hu
    let ρ := P.canonicalRule w c
    have hM := Instance.maximum_le ω.1 hH hxH
    have hp0 := π.rule.reward_nonnegative ω.2.2 Finset.univ ω.1 ω.2.1 hx0
    have hr0 := ρ.reward_nonnegative () Finset.univ ω.1 ω.2.1 hx0
    have hpH := (π.rule.reward_le_maximum ω.2.2 Finset.univ ω.1 ω.2.1).trans hM
    have hrH := (ρ.reward_le_maximum () Finset.univ ω.1 ω.2.1).trans hM
    have hpT0 := π.rule.stoppingTime_nonneg ω.2.2 Finset.univ ω.1 ω.2.1 (fun i => (hu i).1)
    have hrT0 := ρ.stoppingTime_nonneg () Finset.univ ω.1 ω.2.1 (fun i => (hu i).1)
    have hpT1 := π.rule.stoppingTime_le_one ω.2.2 Finset.univ ω.1 ω.2.1
    have hrT1 := ρ.stoppingTime_le_one () Finset.univ ω.1 ω.2.1
    constructor
    · change |π.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1 - ρ.reward () Finset.univ ω.1 ω.2.1| ≤ H
      rw [abs_le]
      constructor <;> linarith
    · change |π.rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 - ρ.stoppingTime () Finset.univ ω.1 ω.2.1| ≤ 1
      rw [abs_le]
      constructor <;> linarith
  exact ⟨hboth.mono fun _ h => h.1, hboth.mono fun _ h => h.2⟩

/-- `cor:score-stability`, for actual policy outcomes. Mean-zero centering is
unnecessary for this inequality, so the statement also applies to general L² scores. -/
theorem RandomizedPolicy.score_stability (π : RandomizedPolicy n) (P : Instance n)
    {H w c I W : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hw : 0 < w) (hc : 0 ≤ c) (score : π.World → ℝ)
    (hscore : MemLp score 2 (P.worldLaw π.seedLaw))
    (hInfo : (∫ ω, score ω ^ 2 ∂P.worldLaw π.seedLaw) ≤ I)
    (hMean : π.expectedOutcomeError P w c ≤ W) :
    |∫ ω, score ω * π.coupledRewardDifference P w c ω ∂P.worldLaw π.seedLaw| +
      |∫ ω, score ω * π.coupledDurationDifference P w c ω ∂P.worldLaw π.seedLaw| ≤
        Real.sqrt (2 * I * (H + 1) * W) := by
  have hm := π.measurable_coupledDifferences P (P.integrable_maximum_of_bounded hbound) hw hc
  have hb := π.coupledDifferences_bounded P (w := w) (c := c) hH hbound
  exact ProphetSecretary.Stability.score_stability_bound_paper (P.worldLaw π.seedLaw) hH hscore
    hm.1.aestronglyMeasurable hm.2.aestronglyMeasurable hb.1 hb.2 hInfo hMean

/-- All likelihood-score products appearing above are integrable. -/
lemma RandomizedPolicy.score_coupledDifferences_integrable (π : RandomizedPolicy n) (P : Instance n)
    {H w c : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hw : 0 < w) (hc : 0 ≤ c) (score : π.World → ℝ)
    (hscore : MemLp score 2 (P.worldLaw π.seedLaw)) :
    Integrable (fun ω => score ω * π.coupledRewardDifference P w c ω) (P.worldLaw π.seedLaw) ∧
      Integrable (fun ω => score ω * π.coupledDurationDifference P w c ω) (P.worldLaw π.seedLaw) := by
  have hm := π.measurable_coupledDifferences P (P.integrable_maximum_of_bounded hbound) hw hc
  have hb := π.coupledDifferences_bounded P (w := w) (c := c) hH hbound
  exact ProphetSecretary.Stability.score_products_integrable (P.worldLaw π.seedLaw) hscore
    hm.1.aestronglyMeasurable hm.2.aestronglyMeasurable hb.1 hb.2

end ProphetSecretary.Model
