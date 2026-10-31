import ProphetSecretary.Model.AcceptanceBound

/-!
# Uniform survival from an acceptance bound

No acceptance forces stopping time one. Thus its probability supplies a lower
bound on survival at every elapsed time in [0,1], without conditioning on any
future observations. This converts the acceptance estimate used in `upmom:selection`.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma RandomizedPolicy.measurableSet_acceptance (π : RandomizedPolicy n) :
    MeasurableSet {ω : π.World | ∃ i, π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i} := by
  rw [setOf_exists]
  exact MeasurableSet.iUnion fun i => π.rule.measurableSet_actualSelects π.measurable_rule
    (by fun_prop) (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i

lemma RandomizedPolicy.oneResponse_eq_acceptanceProbability (π : RandomizedPolicy n) (P : Instance n) :
    π.selectedResponse P (fun _ _ => 1) =
      (P.worldLaw π.seedLaw).real {ω : π.World | ∃ i,
        π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i} := by
  unfold selectedResponse
  simp_rw [Policy.mappedReward_one_eq_acceptanceIndicator]
  simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_setOf_eq] using
    (integral_indicator_one (μ := P.worldLaw π.seedLaw) π.measurableSet_acceptance)

/-- This general-policy comparison uses only the convention τ=1 on no acceptance. -/
theorem RandomizedPolicy.survivalProbability_ge_noAcceptance (π : RandomizedPolicy n)
    (P : Instance n) {t : ℝ} (ht : t ≤ 1) :
    1 - π.selectedResponse P (fun _ _ => 1) ≤
      (P.worldLaw π.seedLaw).real {ω : π.World | t ≤ π.realizedDuration ω} := by
  let E : Set π.World := {ω | ∃ i, π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i}
  have hsub : Eᶜ ⊆ {ω : π.World | t ≤ π.realizedDuration ω} := by
    intro ω hω
    have hn : ∀ i, ¬π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i :=
      fun i hi => hω ⟨i, hi⟩
    have heq := π.rule.stoppingTime_eq_one_of_no_actualSelection ω.2.2 Finset.univ ω.1 ω.2.1 hn
    change t ≤ π.rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
    rw [heq]
    exact ht
  have hm := measureReal_mono hsub (μ := P.worldLaw π.seedLaw)
  rw [measureReal_compl π.measurableSet_acceptance, probReal_univ,
    ← π.oneResponse_eq_acceptanceProbability P] at hm
  exact hm

/-- The manuscript's uniform survival estimate, before abbreviating its error. -/
theorem Instance.canonical_survivalProbability_lower (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c t : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4) (ht : t ≤ 1) :
    let π := P.valuePolicy (P.integrable_maximum_of_bounded hcap)
      (hδ.le.trans hwδ) (hδ.le.trans hcδ)
    1 - optimalCompetitiveRatio -
      (scalarGap P w c / (w * h) + (32 / δ) * (1 + P.positiveCount) ^ 2 * h / w) -
        (2 * w / c) * P.positiveCount * h ≤
      (P.worldLaw π.seedLaw).real {ω : π.World | t ≤ π.realizedDuration ω} := by
  have ha := P.canonical_acceptanceResponse_le hcap hδ hwδ hcδ hsum hh hquarter
  have hs := (P.valuePolicy (P.integrable_maximum_of_bounded hcap)
    (hδ.le.trans hwδ) (hδ.le.trans hcδ)).survivalProbability_ge_noAcceptance P ht
  dsimp only at ha ⊢
  linarith only [ha, hs]

end ProphetSecretary.Model
