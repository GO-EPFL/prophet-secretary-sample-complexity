import ProphetSecretary.Model.BellmanResidualStep
import ProphetSecretary.Model.BellmanResidualPath
import ProphetSecretary.Model.ClockConditionalReach
import ProphetSecretary.Model.BellmanLossProbability

/-!
# Cross-law Bellman residual identity

Paper correspondence: `upstat:residual`. The design law `Q` and its scalar weights are
fixed. Online values have true law `P`; the competing policy may use every past identity,
value and timestamp, including zero observations, and independent auxiliary randomness.
The proof uses actual first-step disintegration and finite induction, not a hypothesized
generator or an unbiasedness statement about a data-selected design law.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

/-- Fixed-design value minus true-law policy payoff equals the expected reached sum of
signed transition discrepancies and nonnegative design-law action losses. -/
theorem RandomizedPolicy.bellman_residualIdentity {m : ℕ} (π : RandomizedPolicy m)
    (Q P : Instance m) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue Q w c - π.scalarObjective P w c = π.expectedReachedDesignGap Q P w c := by
  induction m using Nat.strong_induction_on generalizing w c with
  | h m ih =>
    cases m with
    | zero =>
      rw [optimalScalarValue_empty Q w c, π.empty_scalarObjective P w c, sub_self]
      simp [RandomizedPolicy.expectedReachedDesignGap, Policy.reachedDesignGap,
        Policy.reachedTransitionResidual, Policy.reachedBellmanLoss]
    | succ n =>
      rw [π.bellman_firstResidualIdentity Q P hQ hP hw hc]
      unfold RandomizedPolicy.expectedReachedDesignGap
      rw [P.integral_firstStepWorld_iterated π.seedLaw
        (f := fun ω : π.World => π.rule.reachedDesignGap Q P w c ω.2.2 ω.1 ω.2.1)
        (π.rule.measurable_reachedDesignGap π.measurable_rule Q P hQ hP hw hc
          (measurable_snd.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst)
          (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)))
        (π.rule.integrable_reachedDesignGap π.measurable_rule Q P hQ hP π.seedLaw hw hc)]
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [(P.firstPrefix_time_measurePreserving π.seedLaw i).quasiMeasurePreserving.ae
        (Instance.firstChildTimeLaw_mem_unitInterval i)] with p hp
      let D := Q.restrictTo (remainingSet i)
      let T := P.restrictTo (remainingSet i)
      let C := π.rule.fixedContinuationPolicy π.measurable_rule (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)
      have hD := Q.restrictTo_integrable_maximum (remainingSet i) hQ
      have hT := P.restrictTo_integrable_maximum (remainingSet i) hP
      have hct := mul_nonneg hc (sub_nonneg.mpr hp.1.2)
      have hchild := ih (remainingSet i).card (remainingSet_card_lt i) C D T hD hT hw hct
      have hgap : π.rule.bellmanCrossGap Q P i w c p =
          C.expectedReachedDesignGap D T w (c * (1 - p.2.1)) := by
        unfold Policy.bellmanCrossGap Instance.bellmanContinuation
        rw [max_eq_right (sub_nonneg.mpr hp.1.2),
          π.rule.firstContinuationObjective_eq π.measurable_rule P i w c p]
        exact hchild
      rw [hgap]
      exact (π.rule.expectedReachedDesignGap_firstStep π.measurable_rule Q P hQ hP hw hc p i hp.2).symm

/-- The reached-sum form of `upstat:residual`, with every integration obligation
already discharged for finite first-moment product laws. -/
theorem RandomizedPolicy.bellman_residualIdentity_sum {m : ℕ} (π : RandomizedPolicy m)
    (Q P : Instance m) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue Q w c - π.scalarObjective P w c =
      ∫ ω : π.World, ∑ i : Fin m, if π.rule.Reaches ω.2.2 ω.1 ω.2.1 i then
        Q.transitionResidual P w c ω.2.1 i + π.rule.arrivalBellmanLoss Q w c ω.2.2 ω.1 ω.2.1 i else 0
        ∂P.worldLaw π.seedLaw := by
  rw [π.bellman_residualIdentity Q P hQ hP hw hc]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => π.rule.reachedDesignGap_eq_sum Q P w c ω.2.2 ω.1 ω.2.1

noncomputable def RandomizedPolicy.expectedReachedTransitionResidual {m : ℕ} (π : RandomizedPolicy m)
    (Q P : Instance m) (w c : ℝ) : ℝ :=
  ∫ ω : π.World, π.rule.reachedTransitionResidual Q P w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw π.seedLaw

noncomputable def RandomizedPolicy.expectedReachedDesignActionLoss {m : ℕ} (π : RandomizedPolicy m)
    (Q P : Instance m) (w c : ℝ) : ℝ :=
  ∫ ω : π.World, π.rule.reachedBellmanLoss Q w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw π.seedLaw

/-- Separation of the signed residual and action-loss expectations. In particular,
the second expectation is nonnegative under every evaluation law. -/
theorem RandomizedPolicy.bellman_residualIdentity_split {m : ℕ} (π : RandomizedPolicy m)
    (Q P : Instance m) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue Q w c - π.scalarObjective P w c =
      π.expectedReachedTransitionResidual Q P w c + π.expectedReachedDesignActionLoss Q P w c := by
  rw [π.bellman_residualIdentity Q P hQ hP hw hc]
  unfold RandomizedPolicy.expectedReachedDesignGap Policy.reachedDesignGap
  exact integral_add
    (π.rule.integrable_reachedTransitionResidual π.measurable_rule Q P hQ hP π.seedLaw hw hc)
    (π.rule.integrable_reachedBellmanLoss_under π.measurable_rule Q P hQ hP π.seedLaw hw hc)

lemma RandomizedPolicy.expectedReachedDesignActionLoss_nonnegative {m : ℕ} (π : RandomizedPolicy m)
    (Q P : Instance m) (w c : ℝ) : 0 ≤ π.expectedReachedDesignActionLoss Q P w c :=
  integral_nonneg fun ω => π.rule.reachedBellmanLoss_nonnegative Q w c ω.2.2 ω.1 ω.2.1

/-- The manuscript's `E_clocks Σ r_i ξ_i` form, with reach probabilities averaging
true offers and the independent policy seed at each fixed complete clock vector. -/
theorem RandomizedPolicy.bellman_residualIdentity_clocks {m : ℕ} (π : RandomizedPolicy m)
    (Q P : Instance m) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue Q w c - π.scalarObjective P w c =
      (∫ u : Fin m → ℝ, ∑ i : Fin m,
        π.rule.clockConditionalReach P π.seedLaw u i * Q.transitionResidual P w c u i ∂Instance.clocksLaw m) +
        π.expectedReachedDesignActionLoss Q P w c := by
  rw [π.bellman_residualIdentity_split Q P hQ hP hw hc]
  unfold RandomizedPolicy.expectedReachedTransitionResidual
  rw [π.rule.integral_reachedTransitionResidual_eq_clockConditional π.measurable_rule Q P hQ hP π.seedLaw hw hc]

lemma Instance.valuePolicy_expectedDesignActionLoss_zero {m : ℕ} (Q P : Instance m)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (Q.valuePolicy hQ hw.le hc).expectedReachedDesignActionLoss Q P w c = 0 := by
  unfold RandomizedPolicy.expectedReachedDesignActionLoss
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun ω => by
    have hr : ω.2.2 = () := @Subsingleton.elim Unit (inferInstance : Subsingleton Unit) (ω.2.2 : Unit) ()
    change (Q.valuePolicy hQ hw.le hc).rule.reachedBellmanLoss Q w c ω.2.2 ω.1 ω.2.1 = 0
    rw [hr]
    unfold Policy.reachedBellmanLoss
    apply Finset.sum_eq_zero
    intro i _
    have hzero := Q.valueThreshold_arrivalLoss_zero hw c ω.1 ω.2.1 i
    split_ifs
    · exact hzero
    · rfl

/-- A design-optimal canonical policy has no design action losses even when evaluated
under another product law. Its true payoff deficit is exactly the signed residual. -/
theorem Instance.valuePolicy_residualIdentity_clocks {m : ℕ} (Q P : Instance m)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let π := Q.valuePolicy hQ hw.le hc
    optimalScalarValue Q w c - π.scalarObjective P w c =
      ∫ u : Fin m → ℝ, ∑ i : Fin m,
        π.rule.clockConditionalReach P π.seedLaw u i * Q.transitionResidual P w c u i ∂Instance.clocksLaw m := by
  have h := (Q.valuePolicy hQ hw.le hc).bellman_residualIdentity_clocks Q P hQ hP hw hc
  rw [Q.valuePolicy_expectedDesignActionLoss_zero P hQ hw hc, add_zero] at h
  exact h

end ProphetSecretary.Model


