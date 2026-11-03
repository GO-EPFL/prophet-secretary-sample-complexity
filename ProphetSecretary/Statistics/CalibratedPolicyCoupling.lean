import ProphetSecretary.Statistics.CalibratedPolicyQueries
import ProphetSecretary.Statistics.CalibratedPreparedPolicy
import ProphetSecretary.Statistics.CalibrationExactRegret
import ProphetSecretary.Reach.CappedThresholdComparison

/-!
# Numerical coupling for the calibrated grid policies

The conditional query bound controls the actual prefix-max thresholds. The
reference is the exact cap-modified empirical endpoint, with deletion
monotonicity applied to that reference alone.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

noncomputable def policyAccuracy (m : ℕ) (zlo : ℝ) : ℝ :=
  zlo/((m : ℝ)*(1+targetCountCutoff m)^2)

noncomputable def policyFailureBound (n m J : ℕ) : ℝ :=
  1/((m : ℝ)^2*(n : ℝ)*(J+1))

lemma policyBoundaryLoss_le {m : ℕ} [NeZero m] {zlo z LQ LP L : ℝ}
    (hzlo : 0 < zlo) (hz : zlo ≤ z) (hQ0 : 0 ≤ LQ) (hQ : LQ ≤ L)
    (hP : LP ≤ L) :
    (2*(zlo/((m : ℝ)*(1+L)^2))/(z/(1+LQ)))*LP ≤ 2/(m : ℝ) := by
  have hL : 0 ≤ L := hQ0.trans hQ
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hzp : 0 < z := hzlo.trans_le hz
  let a := zlo/z
  let b := (1+LQ)/(1+L)
  let c := LP/(1+L)
  have ha0 : 0 ≤ a := div_nonneg hzlo.le hzp.le
  have ha1 : a ≤ 1 := (div_le_one hzp).mpr hz
  have hb0 : 0 ≤ b := div_nonneg (by linarith) (by linarith)
  have hb1 : b ≤ 1 := (div_le_one (by linarith : 0 < 1+L)).mpr (by linarith)
  have hc1 : c ≤ 1 := (div_le_one (by linarith : 0 < 1+L)).mpr (by linarith)
  calc
    _ = (2/(m : ℝ))*a*b*c := by
      dsimp [a,b,c]
      have hd : 1+L ≠ 0 := by positivity
      have he : 1+LQ ≠ 0 := by positivity
      field_simp
    _ ≤ (2/(m : ℝ))*a*b := mul_le_of_le_one_right (by positivity) hc1
    _ ≤ (2/(m : ℝ))*a := mul_le_of_le_one_right (by positivity) hb1
    _ ≤ _ := mul_le_of_le_one_right (by positivity) ha1

variable {n m J : ℕ} [NeZero n] [NeZero m] {PSeed : Type} [MeasurableSpace PSeed]

lemma policyFailureBound_mul_slots : (n : ℝ)*(J+1)*policyFailureBound n m J = 1/(m : ℝ)^2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hJ : (J : ℝ)+1 ≠ 0 := by positivity
  unfold policyFailureBound
  field_simp

/-- At fixed first-block data the estimated endpoint actions disagree with
those of the exact capped reference with probability at most `3/m`. -/
theorem familyActionDisagreement_le (P : Instance n) (ν : Measure PSeed) [IsProbabilityMeasure ν]
    {zlo : ℝ} (hzlo : 0 < zlo) (hord : zlo ≤ 1/4)
    (hz : ∀ l, familyCoefficient zlo (1/4) J l ∈ Icc zlo (1/4 : ℝ))
    (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (y : Reservoir n m) (hy : ∀ i l, 0 ≤ y i l)
    (hQ : (totalEmpiricalInstance y).positiveCount ≤ targetCountCutoff m)
    (hP : P.positiveCount ≤ targetCountCutoff m)
    (hconf : ∀ (A : Finset (Fin n)) (u z : ℝ), u ∈ Icc (0 : ℝ) 1 → z ∈ Icc (0 : ℝ) 4 →
      ν.real {s | policyAccuracy m zlo < |estimate y A u z s - (totalEmpiricalInstance y).continuationValue A u 1 z|} ≤
        policyFailureBound n m J) (j : Fin (J+1)) :
    let θ : PolicyQueryArray n J PSeed → ℝ → Fin n → History n → ℝ :=
      fun r => familyThreshold zlo (1/4) estimate j (y,r)
    (P.worldLaw (policyQueryArrayLaw (n := n) (J := J) ν)).real {ω |
      (cappedHistoryThresholdPolicy θ).actionDisagreement
        (canonicalCappedPolicy (totalEmpiricalInstance y) (familyCoefficient zlo (1/4) J j.val))
        ω.2.2 ω.1 ω.2.1} ≤ 3/(m : ℝ) := by
  dsimp only
  let Q := totalEmpiricalInstance y
  let z := familyCoefficient zlo (1/4) J j.val
  let νa := policyQueryArrayLaw (n := n) (J := J) ν
  let θ : PolicyQueryArray n J PSeed → ℝ → Fin n → History n → ℝ :=
    fun r => familyThreshold zlo (1/4) estimate j (y,r)
  have hh : 0 ≤ policyAccuracy m zlo := by unfold policyAccuracy; positivity
  have hevent := familyThresholdError_probability_le P ν hord estimate he y hy hh
    (fun l => ⟨hzlo.le.trans (hz l).1, (hz l).2.trans (by norm_num)⟩) hconf j
  rw [policyFailureBound_mul_slots] at hevent
  have hd := cappedThreshold_actionDisagreement_probability Q P (totalEmpiricalInstance_integrable y)
    νa θ (hzlo.trans_le (hz j.val).1) hh
  have hb := policyBoundaryLoss_le (m := m) hzlo (hz j.val).1 (Q.tailCount_nonnegative 0) hQ hP
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hmpos : (0 : ℝ) < m := by linarith
  have hInv : 1/(m : ℝ)^2 ≤ 1/(m : ℝ) :=
    div_le_div_of_nonneg_left zero_le_one hmpos (by nlinarith)
  change (P.worldLaw νa).real {ω |
    (cappedHistoryThresholdPolicy θ).actionDisagreement (canonicalCappedPolicy Q z)
      ω.2.2 ω.1 ω.2.1} ≤ _
  apply hd.trans
  change (P.worldLaw νa).real {ω | ∃ i, policyAccuracy m zlo <
      |familyThreshold zlo (1/4) estimate j (y,ω.2.2) (ω.2.1 i) i
        (history Finset.univ ω.1 ω.2.1 (ω.2.1 i)) - Q.continuationAtArrival 1 z ω.1 ω.2.1 i|} +
    (2*policyAccuracy m zlo/(z/(1+Q.positiveCount)))*P.positiveCount ≤ _
  have hb' : (2*policyAccuracy m zlo/(z/(1+Q.positiveCount)))*P.positiveCount ≤ 2/(m : ℝ) := hb
  apply (add_le_add (hevent.trans hInv) hb').trans
  ring_nf
  exact le_rfl

variable (P : Instance n) (ν : Measure PSeed) [IsProbabilityMeasure ν]
  {zlo : ℝ} (hzlo : 0 < zlo) (hord : zlo ≤ 1/4)
  (hz : ∀ l, familyCoefficient zlo (1/4) J l ∈ Icc zlo (1/4 : ℝ))
  (estimate : ContinuationEstimator n m PSeed)
  (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
    estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
  (y : Reservoir n m) (hy : ∀ i l, 0 ≤ y i l)
  (hP : P.positiveCount ≤ targetCountCutoff m)
  (hconf : (totalEmpiricalInstance y).positiveCount ≤ targetCountCutoff m → ∀ (A : Finset (Fin n)) (u z : ℝ), u ∈ Icc (0 : ℝ) 1 → z ∈ Icc (0 : ℝ) 4 →
    ν.real {s | policyAccuracy m zlo < |estimate y A u z s - (totalEmpiricalInstance y).continuationValue A u 1 z|} ≤
      policyFailureBound n m J)
  (j : Fin (J+1))

omit [NeZero n] [MeasurableSpace PSeed] in
lemma frozenFamilyPolicy_eq_capped (hf : ¬ familyFallback y) :
    frozenFamilyPolicy zlo (1/4) estimate y j =
      cappedHistoryThresholdPolicy (fun r => familyThreshold zlo (1/4) estimate j (y,r)) := by
  unfold frozenFamilyPolicy numericalFamilyPolicy
  simp only [hf, if_false, cappedHistoryThresholdPolicy]

include hzlo hord hz he hy hP hconf

/-- Numerical policies need not be deletion monotone; transfer both
observables from the exact policy on the common execution. -/
theorem frozenFamilyPolicy_duration_le_reach (i : Fin n) :
    let π := frozenFamilyPolicy zlo (1/4) estimate y j
    let νa := policyQueryArrayLaw (n := n) (J := J) ν
    π.meanDuration P νa ≤ π.reachProbability P νa i + 6/(m : ℝ) := by
  dsimp only
  let π := frozenFamilyPolicy zlo (1/4) estimate y j
  let νa := policyQueryArrayLaw (n := n) (J := J) ν
  have hπ : π.IsMeasurable := frozenFamilyPolicy_isMeasurable zlo (1/4) estimate he y j
  change π.meanDuration P νa ≤ π.reachProbability P νa i + _
  by_cases hf : familyFallback y
  · let a : PolicyQueryArray n J PSeed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool :=
      fun _ _ _ _ x => decide (x=1)
    have heq : π = markovPolicy a := by
      simp [π, frozenFamilyPolicy, numericalFamilyPolicy, hf, markovPolicy, a]
    have hmono : DeletionMonotoneAcceptance a := by
      intro _ _ _ _ _ _ _ _ _ _
      exact id
    rw [heq] at hπ ⊢
    exact (markovPolicy.meanDuration_le_reachProbability a hmono hπ P νa i).trans
      (le_add_of_nonneg_right (by positivity))
  · let Q := totalEmpiricalInstance y
    let z := familyCoefficient zlo (1/4) J j.val
    let σ : Policy (PolicyQueryArray n J PSeed) n := canonicalCappedPolicy Q z
    have hQ : Q.positiveCount ≤ targetCountCutoff m := by
      have h := not_or.mp hf
      apply le_of_not_gt
      simpa only [empiricalPositiveCount_eq, trainingInstance, MeasurableEquiv.symm_apply_apply, Q] using h.1
    have hd := familyActionDisagreement_le P ν hzlo hord hz estimate he y hy hQ hP (hconf hQ) j
    dsimp only at hd
    rw [← frozenFamilyPolicy_eq_capped (zlo := zlo) estimate y j hf] at hd
    change (P.worldLaw νa).real {ω | π.actionDisagreement σ ω.2.2 ω.1 ω.2.1} ≤ _ at hd
    have hz0 : 0 ≤ z := hzlo.le.trans (hz j.val).1
    have hm := canonicalCappedPolicy_isMeasurable (Seed := PolicyQueryArray n J PSeed) Q
      (totalEmpiricalInstance_integrable y) hz0
    have hT := π.meanDuration_sub_le_disagreement σ hπ hm P νa
    have hq := π.reachProbability_reverse_le_disagreement σ P νa i
    have hTq := canonicalCappedPolicy_meanDuration_le_reach Q P
      (totalEmpiricalInstance_integrable y) νa hz0 i
    change σ.meanDuration P νa ≤ σ.reachProbability P νa i at hTq
    have h₁ : π.meanDuration P νa ≤ σ.meanDuration P νa + 3/(m : ℝ) := by
      exact (sub_le_iff_le_add.mp (hT.trans hd)).trans_eq (add_comm _ _)
    have h₂ := hTq.trans (hq.trans (add_le_add le_rfl hd))
    calc
      _ ≤ σ.meanDuration P νa + 3/(m : ℝ) := h₁
      _ ≤ (π.reachProbability P νa i + 3/(m : ℝ)) + 3/(m : ℝ) := add_le_add h₂ le_rfl
      _ = _ := by ring

/-- At count-good first-block data, changing the exact capped endpoint to
the numerical one loses at most `4/m` in the true scalar objective. -/
theorem frozenFamilyPolicy_scalarObjective_loss_le
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    (hQ : (totalEmpiricalInstance y).positiveCount ≤ targetCountCutoff m) :
    let z := familyCoefficient zlo (1/4) J j.val
    (exactCalibrationEndpoint y z).scalarObjective P 1 z -
      (RandomizedPolicy.ofRule (policyQueryArrayLaw ν) (frozenFamilyPolicy zlo (1/4) estimate y j)
        (frozenFamilyPolicy_isMeasurable zlo (1/4) estimate he y j)).scalarObjective P 1 z ≤ 4/(m : ℝ) := by
  dsimp only
  let Q := totalEmpiricalInstance y
  let z := familyCoefficient zlo (1/4) J j.val
  let νa := policyQueryArrayLaw (n := n) (J := J) ν
  let π := frozenFamilyPolicy zlo (1/4) estimate y j
  let πe := exactCalibrationEndpoint y z
  let f : PolicyQueryArray n J PSeed → πe.Seed := fun _ => ()
  let πa := πe.pullbackSeed νa f measurable_const
  have hfLaw : MeasurePreserving f νa πe.seedLaw := by
    refine ⟨measurable_const, ?_⟩
    change νa.map (fun _ => ()) = Measure.dirac ()
    rw [Measure.map_const, measure_univ, one_smul]
  have hi := P.integrable_maximum_of_bounded hcap
  have hLift : πa.scalarObjective P 1 z = πe.scalarObjective P 1 z := by
    rw [πa.scalarObjective_eq P hi, πe.scalarObjective_eq P hi,
      πe.pullbackSeed_expectedReward νa f measurable_const hfLaw P,
      πe.pullbackSeed_expectedDuration νa f measurable_const hfLaw P]
  have hz0 : 0 ≤ z := hzlo.le.trans (hz j.val).1
  have hz1 : z ≤ 1/4 := (hz j.val).2
  have hπ : π.IsMeasurable := frozenFamilyPolicy_isMeasurable zlo (1/4) estimate he y j
  change πe.scalarObjective P 1 z - (RandomizedPolicy.ofRule νa π hπ).scalarObjective P 1 z ≤ _
  rw [← hLift]
  have hdec (r : PolicyQueryArray n J PSeed) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
      πa.rule.decide r t i x H = decide (0 < x ∧ empiricalCapThreshold y z (unseen H) t i ≤ x) :=
    exactCalibrationEndpoint_decide y z () t i x H
  by_cases hM : (totalEmpiricalInstance y).expectedMaximum ≤ 1/4
  · have hf : ¬ familyFallback y := by
      apply not_or.mpr
      refine ⟨not_lt.mpr ?_, not_lt.mpr hM⟩
      simpa only [empiricalPositiveCount_eq, trainingInstance, MeasurableEquiv.symm_apply_apply, Q] using hQ
    let σ : Policy (PolicyQueryArray n J PSeed) n := canonicalCappedPolicy Q z
    have hσ := canonicalCappedPolicy_isMeasurable (Seed := PolicyQueryArray n J PSeed) Q
      (totalEmpiricalInstance_integrable y) hz0
    have ha : ∀ᵐ ω : World n (PolicyQueryArray n J PSeed) ∂P.worldLaw νa, ∀ i,
        πa.rule.action ω.2.2 Finset.univ ω.1 ω.2.1 i = σ.action ω.2.2 Finset.univ ω.1 ω.2.1 i := by
      filter_upwards [P.world_clocks_mem_unitInterval νa] with ω hu i
      change πa.rule.decide ω.2.2 (ω.2.1 i) i (ω.1 i) _ = σ.decide ω.2.2 (ω.2.1 i) i (ω.1 i) _
      rw [hdec]
      by_cases hx : ω.1 i = 1
      · have ha : 0 < ω.1 i ∧ empiricalCapThreshold y z
              (unseen (history Finset.univ ω.1 ω.2.1 (ω.2.1 i))) (ω.2.1 i) i ≤ ω.1 i := by
            rw [hx]
            exact ⟨zero_lt_one, empiricalCapThreshold_le_one y hz0 hz1 (hu i).1 _ _⟩
        rw [decide_eq_true ha]
        simp [σ, canonicalCappedPolicy, cappedHistoryThresholdPolicy, hx]
      · simp only [σ, canonicalCappedPolicy, canonicalCappedThreshold, cappedHistoryThresholdPolicy, hx, false_or]
        unfold empiricalCapThreshold
        rw [if_pos hM, empiricalValueThreshold_eq y zero_lt_one hz0]
    have hs := RandomizedPolicy.ofRule_scalarObjective_eq_of_actions_eq_ae P νa πa.rule σ
      πa.measurable_rule hσ ha 1 z
    change (RandomizedPolicy.ofRule νa πa.rule πa.measurable_rule).scalarObjective P 1 z - _ ≤ _
    rw [hs]
    have hd := familyActionDisagreement_le P ν hzlo hord hz estimate he y hy hQ hP (hconf hQ) j
    dsimp only at hd
    rw [← frozenFamilyPolicy_eq_capped (zlo := zlo) estimate y j hf] at hd
    change (P.worldLaw νa).real {ω | π.actionDisagreement σ ω.2.2 ω.1 ω.2.1} ≤ _ at hd
    have hD := RandomizedPolicy.ofRule_scalarObjective_sub_le_disagreement P hcap νa π σ hπ hσ hz0
    exact hD.trans ((mul_le_mul_of_nonneg_left hd (by positivity)).trans (by
      have h : (1+z)*3 ≤ 4 := by linarith
      simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h (by positivity : (0 : ℝ) ≤ m)))
  · have hf : familyFallback y := Or.inr (lt_of_not_ge hM)
    have hv := (measurePreserving_fst (μ := P.valuesLaw)
      (ν := (Instance.clocksLaw n).prod νa)).quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun i => (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hcap i)))
    have ha : ∀ᵐ ω : World n (PolicyQueryArray n J PSeed) ∂P.worldLaw νa, ∀ i,
        πa.rule.action ω.2.2 Finset.univ ω.1 ω.2.1 i = π.action ω.2.2 Finset.univ ω.1 ω.2.1 i := by
      filter_upwards [hv] with ω hw i
      change πa.rule.decide ω.2.2 (ω.2.1 i) i (ω.1 i) _ = π.decide ω.2.2 (ω.2.1 i) i (ω.1 i) _
      rw [hdec]
      simp only [π, frozenFamilyPolicy, numericalFamilyPolicy, if_pos hf, empiricalCapThreshold, if_neg hM]
      congr 1
      apply propext
      refine ⟨fun h => (hw i).antisymm h.2, ?_⟩
      intro h
      rw [h]
      exact ⟨zero_lt_one, le_rfl⟩
    have hs := RandomizedPolicy.ofRule_scalarObjective_eq_of_actions_eq_ae P νa πa.rule π
      πa.measurable_rule hπ ha 1 z
    change (RandomizedPolicy.ofRule νa πa.rule πa.measurable_rule).scalarObjective P 1 z - _ ≤ _
    rw [hs, sub_self]
    positivity

end ProphetSecretary.Statistics.Calibration
