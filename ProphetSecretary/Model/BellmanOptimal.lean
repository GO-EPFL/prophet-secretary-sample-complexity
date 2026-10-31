import ProphetSecretary.Model.BellmanValue

/-!
# Finite Bellman optimization

The upper comparison permits every measurable history-dependent randomized
policy. The canonical value-threshold rule is compared with that same supremum.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma RandomizedPolicy.scalarObjective_eq_firstStep (π : RandomizedPolicy (n + 1))
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw) (w c : ℝ) :
    π.scalarObjective P w c = ∑ i : Fin (n + 1),
      ∫ p : Instance.FirstPrefixData π.Seed, π.rule.firstStepObjective P i w c p
        ∂π.seedLaw.prod ((Instance.firstChildTimeLaw i).prod (P.law i)) := by
  have hm : Measurable (fun ω : π.World ↦ w * π.realizedReward ω + c * π.realizedDuration ω) :=
    (measurable_const.mul π.measurable_realizedReward).add (measurable_const.mul π.measurable_realizedDuration)
  have hi := ((π.integrable_realizedReward P hP).const_mul w).add ((π.integrable_realizedDuration P).const_mul c)
  exact P.integral_firstStepWorld_iterated π.seedLaw hm hi

lemma RandomizedPolicy.integrable_firstStepObjective (π : RandomizedPolicy (n + 1))
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) (w c : ℝ) :
    Integrable (π.rule.firstStepObjective P i w c)
      (π.seedLaw.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) := by
  have hi := ((π.integrable_realizedReward P hP).const_mul w).add ((π.integrable_realizedDuration P).const_mul c)
  exact (P.integrable_firstStepWorld π.seedLaw i hi).integral_prod_left

namespace Instance

lemma firstPrefix_time_measurePreserving {S : Type*} [MeasurableSpace S]
    (P : Instance (n + 1)) (ν : Measure S) [IsProbabilityMeasure ν] (i : Fin (n + 1)) :
    MeasurePreserving (fun p : FirstPrefixData S ↦ p.2.1)
      (ν.prod ((firstChildTimeLaw i).prod (P.law i))) (firstChildTimeLaw i) :=
  (measurePreserving_fst (μ := firstChildTimeLaw i) (ν := P.law i)).comp
    (measurePreserving_snd (μ := ν) (ν := (firstChildTimeLaw i).prod (P.law i)))

lemma integral_bellmanPrefix {S : Type*} [MeasurableSpace S]
    (P : Instance (n + 1)) (ν : Measure S) [IsProbabilityMeasure ν]
    (hP : Integrable maximum P.valuesLaw) (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (∫ p : FirstPrefixData S, P.bellmanFirstPayoff i w c p.2
      ∂ν.prod ((firstChildTimeLaw i).prod (P.law i))) =
      ∫ z, P.bellmanFirstPayoff i w c z ∂(firstChildTimeLaw i).prod (P.law i) := by
  have hp := measurePreserving_snd (μ := ν) (ν := (firstChildTimeLaw i).prod (P.law i))
  have h := integral_map (μ := ν.prod ((firstChildTimeLaw i).prod (P.law i))) hp.measurable.aemeasurable
    (P.measurable_bellmanFirstPayoff hP i hw hc).aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h.symm

end Instance

lemma RandomizedPolicy.firstStepObjective_integral_le_bellman (π : RandomizedPolicy (n + 1))
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (∫ p : Instance.FirstPrefixData π.Seed, π.rule.firstStepObjective P i w c p
      ∂π.seedLaw.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) ≤
      ∫ z, P.bellmanFirstPayoff i w c z ∂(Instance.firstChildTimeLaw i).prod (P.law i) := by
  have hpoint : ∀ᵐ p : Instance.FirstPrefixData π.Seed
      ∂π.seedLaw.prod ((Instance.firstChildTimeLaw i).prod (P.law i)),
      π.rule.firstStepObjective P i w c p ≤ P.bellmanFirstPayoff i w c p.2 := by
    filter_upwards [(P.firstPrefix_time_measurePreserving π.seedLaw i).quasiMeasurePreserving.ae
      (Instance.firstChildTimeLaw_mem_unitInterval i)] with p hp
    have h := π.rule.firstStepObjective_le_bellman π.measurable_rule P hP i hw hc p hp.2
    simpa only [Instance.bellmanFirstPayoff, Instance.bellmanContinuation,
      max_eq_right (sub_nonneg.mpr hp.1.2)] using h
  have h := integral_mono_ae (π.integrable_firstStepObjective P hP i w c)
    ((P.integrable_bellmanFirstPayoff hP i hw hc).comp_snd π.seedLaw) hpoint
  exact h.trans_eq (P.integral_bellmanPrefix π.seedLaw hP i hw hc)

/-- First-step Bellman upper bound against the full randomized online policy class. -/
lemma RandomizedPolicy.scalarObjective_le_bellmanValue (π : RandomizedPolicy (n + 1))
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    π.scalarObjective P w c ≤ P.bellmanValue w c := by
  rw [π.scalarObjective_eq_firstStep P hP w c]
  exact Finset.sum_le_sum (fun i _hi ↦ π.firstStepObjective_integral_le_bellman P hP i hw hc)

lemma Instance.optimalScalarValue_le_bellmanValue (P : Instance (n + 1))
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue P w c ≤ P.bellmanValue w c := by
  apply csSup_le (scalarValues_nonempty P w c)
  rintro v ⟨π, rfl⟩
  exact π.scalarObjective_le_bellmanValue P hP hw hc

lemma remainingSet_card_lt (i : Fin (n + 1)) : (remainingSet i).card < n + 1 := by
  simpa only [remainingSet, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_erase_lt_of_mem (Finset.mem_univ i))

lemma Instance.valueThreshold_firstAction_iff (P : Instance (n + 1))
    {w c : ℝ} (hw : 0 < w) (i : Fin (n + 1)) (t x : ℝ) :
    (thresholdPolicy (fun (_ : Unit) A s j ↦ P.valueThreshold w c A s j)).firstAction () i t x = true ↔
      P.bellmanContinuation i w c t ≤ w * x := by
  have hu : unseen (fun _ : Fin (n + 1) ↦ (none : Option (ℝ × ℝ))) = Finset.univ := by
    ext j
    simp [unseen]
  change decide (P.valueThreshold w c (unseen (fun _ ↦ none)) t i ≤ x) = true ↔ _
  rw [hu, decide_eq_true_eq]
  change (P.bellmanContinuation i w c t / w ≤ x) ↔ _
  rw [div_le_iff₀ hw, mul_comm x w]

lemma Instance.valueThreshold_firstContinuation_eq (P : Instance (n + 1))
    (hP : Integrable Instance.maximum P.valuesLaw) {w c t : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (ht : t ≤ 1) (i : Fin (n + 1)) (x : ℝ) :
    (thresholdPolicy (fun (_ : Unit) A s j ↦ P.valueThreshold w c A s j)).firstContinuationObjective
      P i w c ((), t, x) =
      ((P.restrictTo (remainingSet i)).valuePolicy (P.restrictTo_integrable_maximum _ hP) hw
        (mul_nonneg hc (sub_nonneg.mpr ht))).scalarObjective (P.restrictTo (remainingSet i)) w (c * (1 - t)) := by
  rw [Policy.firstContinuationObjective_eq _ (P.valueThreshold_policy_isMeasurable hP hw hc)]
  exact P.valuePolicy_continuationObjective hP hw hc ht (remainingSet i) (firstPrefix i t x)
    (validPrefix_firstPrefix i t x)

/-- The explicit induction step: canonical child objective equalities imply
the parent's Bellman first-step equality. The child equalities are discharged
by strong induction in `valuePolicy_optimal` below. -/
lemma Instance.valuePolicy_bellman_step (P : Instance (n + 1))
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hChild : ∀ (i : Fin (n + 1)) (d : ℝ) (hd : 0 ≤ d),
      ((P.restrictTo (remainingSet i)).valuePolicy (P.restrictTo_integrable_maximum _ hP) hw.le hd).scalarObjective
        (P.restrictTo (remainingSet i)) w d = optimalScalarValue (P.restrictTo (remainingSet i)) w d) :
    (P.valuePolicy hP hw.le hc).scalarObjective P w c = P.bellmanValue w c := by
  let π := P.valuePolicy hP hw.le hc
  let ρ : Policy Unit (n + 1) := thresholdPolicy (fun (_ : Unit) A t i ↦ P.valueThreshold w c A t i)
  have hρ : ρ.IsMeasurable := P.valueThreshold_policy_isMeasurable hP hw.le hc
  rw [π.scalarObjective_eq_firstStep P hP w c]
  change (∑ i : Fin (n + 1), ∫ p : Instance.FirstPrefixData Unit,
    ρ.firstStepObjective P i w c p ∂(Measure.dirac ()).prod
      ((Instance.firstChildTimeLaw i).prod (P.law i))) =
    ∑ i : Fin (n + 1), ∫ z, P.bellmanFirstPayoff i w c z
      ∂(Instance.firstChildTimeLaw i).prod (P.law i)
  apply Finset.sum_congr rfl
  intro i _hi
  have heq : (ρ.firstStepObjective P i w c) =ᵐ[(Measure.dirac ()).prod
      ((Instance.firstChildTimeLaw i).prod (P.law i))]
      (fun p : Instance.FirstPrefixData Unit ↦ P.bellmanFirstPayoff i w c p.2) := by
    filter_upwards [(P.firstPrefix_time_measurePreserving (Measure.dirac ()) i).quasiMeasurePreserving.ae
      (Instance.firstChildTimeLaw_mem_unitInterval i)] with p hp
    rcases p with ⟨r, t, x⟩
    cases r
    let Q := P.restrictTo (remainingSet i)
    have hct : 0 ≤ c * (1 - t) := mul_nonneg hc (sub_nonneg.mpr hp.1.2)
    have hchild := hChild i (c * (1 - t)) hct
    have hcont := P.valueThreshold_firstContinuation_eq hP hw.le hc hp.1.2 i x
    change ρ.firstContinuationObjective P i w c ((), t, x) = _ at hcont
    rw [hchild] at hcont
    rw [ρ.firstDecision_expected hρ P hP i w c ((), t, x) hp.2, hcont]
    have hclip : P.bellmanContinuation i w c t = optimalScalarValue Q w (c * (1 - t)) := by
      unfold Instance.bellmanContinuation
      rw [max_eq_right (sub_nonneg.mpr hp.1.2)]
    have hact := P.valueThreshold_firstAction_iff (c := c) hw i t x
    change (ρ.firstAction () i t x = true ↔ P.bellmanContinuation i w c t ≤ w * x) at hact
    rw [hclip] at hact
    change (c * t + if ρ.firstAction () i t x = true then w * x else optimalScalarValue Q w (c * (1 - t))) =
      c * t + max (w * x) (P.bellmanContinuation i w c t)
    rw [hclip]
    by_cases ha : optimalScalarValue Q w (c * (1 - t)) ≤ w * x
    · rw [if_pos (hact.mpr ha), max_eq_left ha]
    · rw [if_neg (fun hh ↦ ha (hact.mp hh)), max_eq_right (le_of_not_ge ha)]
  rw [integral_congr_ae heq]
  exact P.integral_bellmanPrefix (Measure.dirac ()) hP i hw.le hc

/-- The measurable finite value-threshold policy attains the scalar optimum
against every admissible randomized history-dependent competitor. The proof
uses strong induction on the number of remaining identities. -/
theorem Instance.valuePolicy_optimal {m : ℕ} (P : Instance m)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (P.valuePolicy hP hw.le hc).scalarObjective P w c = optimalScalarValue P w c := by
  induction m using Nat.strong_induction_on generalizing w c with
  | h m ih =>
    cases m with
    | zero =>
      exact ((P.valuePolicy hP hw.le hc).empty_scalarObjective P w c).trans
        (optimalScalarValue_empty P w c).symm
    | succ n =>
      have hcanonical := P.valuePolicy_bellman_step hP hw hc (fun i d hd ↦
        ih (remainingSet i).card (remainingSet_card_lt i) (P.restrictTo (remainingSet i))
          (P.restrictTo_integrable_maximum _ hP) hw hd)
      apply le_antisymm (scalarObjective_le_optimal _ P hP hw.le hc)
      rw [hcanonical]
      exact P.optimalScalarValue_le_bellmanValue hP hw.le hc

/-- The actual canonical objective equals the Bellman functional, with every
child optimizer obligation discharged by the finite optimizer theorem. -/
theorem Instance.valuePolicy_eq_bellmanValue (P : Instance (n + 1))
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (P.valuePolicy hP hw.le hc).scalarObjective P w c = P.bellmanValue w c :=
  P.valuePolicy_bellman_step hP hw hc (fun i d hd ↦
    (P.restrictTo (remainingSet i)).valuePolicy_optimal (P.restrictTo_integrable_maximum _ hP) (c := d) hw hd)

/-- The finite Bellman equation follows from the independently proved optimizer,
not from a definition of the optimal value or an assumed dynamic program. -/
theorem Instance.optimalScalarValue_eq_bellmanValue (P : Instance (n + 1))
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue P w c = P.bellmanValue w c :=
  (P.valuePolicy_optimal hP hw hc).symm.trans (P.valuePolicy_eq_bellmanValue hP hw hc)

end ProphetSecretary.Model
