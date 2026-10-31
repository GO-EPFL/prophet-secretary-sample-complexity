import ProphetSecretary.Model.BellmanPathLoss

/-!
# Expected reached-action losses

The action-loss sum is jointly measurable and integrable under the actual
independent instance law. These obligations precede the finite recursive
performance-difference identity.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed Ω : Type*} [MeasurableSpace Seed] [MeasurableSpace Ω]

lemma Instance.measurable_continuationAtArrival (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    {x u : Ω → Fin n → ℝ} (hx : ∀ j, Measurable fun ω ↦ x ω j)
    (hu : ∀ j, Measurable fun ω ↦ u ω j) (i : Fin n) :
    Measurable (fun ω ↦ P.continuationAtArrival w c (x ω) (u ω) i) := by
  have hA := measurable_unseen.comp (measurable_history Finset.univ hx hu (hu i))
  have hθ := (P.valueThreshold_jointMeasurable hP hw.le hc).comp
    (hA.prodMk ((measurable_const (a := i)).prodMk (hu i)))
  convert (measurable_const (a := w)).mul hθ using 1
  funext ω
  exact P.continuationAtArrival_eq_threshold hw c (x ω) (u ω) i

lemma Policy.measurable_arrivalBellmanLoss (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ j, Measurable fun ω ↦ x ω j) (hu : ∀ j, Measurable fun ω ↦ u ω j) (i : Fin n) :
    Measurable (fun ω ↦ π.arrivalBellmanLoss P w c (r ω) (x ω) (u ω) i) := by
  have hX : Measurable (fun ω ↦ w * x ω i) := measurable_const.mul (hx i)
  have hV := P.measurable_continuationAtArrival hP hw hc hx hu i
  have he : MeasurableSet {ω | π.action (r ω) Finset.univ (x ω) (u ω) i = true} :=
    measurableSet_eq_fun (π.measurable_action hπ hr hx hu Finset.univ i) measurable_const
  exact (hX.max hV).sub (Measurable.ite he hX hV)

lemma Policy.measurable_reachedBellmanLoss (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ j, Measurable fun ω ↦ x ω j) (hu : ∀ j, Measurable fun ω ↦ u ω j) :
    Measurable (fun ω ↦ π.reachedBellmanLoss P w c (r ω) (x ω) (u ω)) := by
  apply Finset.measurable_sum
  intro i _hi
  exact Measurable.ite (π.measurableSet_reaches hπ hr hx hu i)
    (π.measurable_arrivalBellmanLoss hπ P hP hw hc hr hx hu i) measurable_const

lemma Instance.continuationAtArrival_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (x u : Fin n → ℝ) (i : Fin n) : 0 ≤ P.continuationAtArrival w c x u i := by
  exact P.continuationValue_nonnegative hP _ (le_max_left _ _) hw hc

lemma Instance.continuationAtArrival_le_initial (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (x u : Fin n → ℝ) (i : Fin n) (ht : 0 ≤ u i) :
    P.continuationAtArrival w c x u i ≤ optimalScalarValue P w c := by
  let A := (unseen (history Finset.univ x u (u i))).erase i
  have hcu0 : 0 ≤ c * max 0 (1 - u i) := mul_nonneg hc (le_max_left _ _)
  have hcu1 : c * max 0 (1 - u i) ≤ c := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (max_le zero_le_one (sub_le_self 1 ht)) hc
  exact (optimalScalarValue_mono (P.restrictTo A) (P.restrictTo_integrable_maximum A hP)
    hw hcu0 le_rfl hcu1).trans
      (optimalScalarValue_restrictBy_le P (stateEmbedding A) hP hw hc)

omit [MeasurableSpace Seed] in
lemma Policy.reachedBellmanLoss_le_sum (π : Policy Seed n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (r : Seed) (x u : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hu : ∀ i, 0 ≤ u i) :
    π.reachedBellmanLoss P w c r x u ≤ ∑ i : Fin n, (w * x i + optimalScalarValue P w c) := by
  have hV0 := optimalScalarValue_nonnegative P hP hw hc
  apply Finset.sum_le_sum
  intro i _hi
  have hX0 : 0 ≤ w * x i := mul_nonneg hw (hx i)
  have hL : π.arrivalBellmanLoss P w c r x u i ≤ w * x i + optimalScalarValue P w c := by
    have hv0 := P.continuationAtArrival_nonnegative hP hw hc x u i
    have hv1 := P.continuationAtArrival_le_initial hP hw hc x u i (hu i)
    have hmax : max (w * x i) (P.continuationAtArrival w c x u i) ≤
        w * x i + P.continuationAtArrival w c x u i := max_le (by linarith) (by linarith)
    unfold Policy.arrivalBellmanLoss
    have hchoice : 0 ≤ if π.action r Finset.univ x u i = true then w * x i else
        P.continuationAtArrival w c x u i := by split_ifs <;> assumption
    exact (sub_le_self _ hchoice).trans (hmax.trans (add_le_add le_rfl hv1))
  split_ifs
  · exact hL
  · exact add_nonneg hX0 hV0

lemma Policy.integrable_reachedBellmanLoss (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (fun ω : World n Seed ↦ π.reachedBellmanLoss P w c ω.2.2 ω.1 ω.2.1) (P.worldLaw ν) := by
  have hp : MeasurePreserving (fun ω : World n Seed ↦ ω.1) (P.worldLaw ν) P.valuesLaw :=
    measurePreserving_fst
  have hB : Integrable (fun ω : World n Seed ↦ ∑ i : Fin n,
      (w * ω.1 i + optimalScalarValue P w c)) (P.worldLaw ν) := by
    apply integrable_finsetSum
    intro i _hi
    exact ((hp.integrable_comp_of_integrable (P.integrable_coordinate_of_maximum hP i)).const_mul w).add
      (integrable_const _)
  apply hB.mono' (π.measurable_reachedBellmanLoss hπ P hP hw hc
    (measurable_snd.comp measurable_snd) (fun i ↦ (measurable_pi_apply i).comp measurable_fst)
    (fun i ↦ (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))).aestronglyMeasurable
  filter_upwards [hp.quasiMeasurePreserving.ae P.ae_nonnegative, P.world_clocks_mem_unitInterval ν] with ω hx hu
  rw [Real.norm_eq_abs, abs_of_nonneg (π.reachedBellmanLoss_nonnegative P w c _ _ _)]
  exact π.reachedBellmanLoss_le_sum P hP hw.le hc ω.2.2 ω.1 ω.2.1 hx (fun i ↦ (hu i).1)

noncomputable def RandomizedPolicy.expectedReachedBellmanLoss (π : RandomizedPolicy n)
    (P : Instance n) (w c : ℝ) : ℝ :=
  ∫ ω : π.World, π.rule.reachedBellmanLoss P w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw π.seedLaw

lemma integral_unitReachedBellmanLoss {m : ℕ} (Q : Instance m)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (π : Policy Unit m) (hπ : π.IsMeasurable)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ ω : World m Unit, π.reachedBellmanLoss Q w c ω.2.2 ω.1 ω.2.1 ∂Q.worldLaw (Measure.dirac ())) =
      ∫ z : (Fin m → ℝ) × (Fin m → ℝ), π.reachedBellmanLoss Q w c () z.1 z.2
        ∂Q.valuesLaw.prod (Instance.clocksLaw m) := by
  have hm := π.measurable_reachedBellmanLoss hπ Q hQ hw hc
    (measurable_snd.comp measurable_snd) (fun i ↦ (measurable_pi_apply i).comp measurable_fst)
    (fun i ↦ (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hp := Q.addUnitSeed_measurePreserving
  have h := integral_map (μ := Q.valuesLaw.prod (Instance.clocksLaw m)) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h

/-- Average the actual pathwise loss recursion over the independent residual
future. The rejected child is an admissible fixed-prefix policy. -/
lemma Policy.expectedReachedLoss_firstStep (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (p : Instance.FirstPrefixData Seed)
    (i : Fin (n + 1)) (ht : p.2.1 < 1) :
    (∫ z : Instance.FirstFutureData i,
      π.reachedBellmanLoss P w c p.1 (insertCandidate i (p.2.2, z.1))
        (Instance.firstChildClocks i (p.2.1, z.2)) ∂P.firstFutureLaw i) =
      π.bellmanActionLoss P i w c p + if π.firstAction p.1 i p.2.1 p.2.2 = true then 0 else
        (π.fixedContinuationPolicy hπ (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)).expectedReachedBellmanLoss
          (P.restrictTo (remainingSet i)) w (c * (1 - p.2.1)) := by
  let Q := P.restrictTo (remainingSet i)
  let C := π.fixedContinuationPolicy hπ (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)
  have hQ := P.restrictTo_integrable_maximum (remainingSet i) hP
  have hct := mul_nonneg hc (sub_nonneg.mpr ht.le)
  have hInt : Integrable (fun z : Instance.FirstFutureData i ↦
      (π.fixedContinuation (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)).reachedBellmanLoss
        Q w (c * (1 - p.2.1)) () z.1 z.2) (P.firstFutureLaw i) :=
    Q.addUnitSeed_measurePreserving.integrable_comp_of_integrable
      (C.rule.integrable_reachedBellmanLoss C.measurable_rule Q hQ C.seedLaw hw hct)
  have hChild : C.expectedReachedBellmanLoss Q w (c * (1 - p.2.1)) =
      ∫ z : Instance.FirstFutureData i,
        (π.fixedContinuation (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)).reachedBellmanLoss
          Q w (c * (1 - p.2.1)) () z.1 z.2 ∂P.firstFutureLaw i :=
    integral_unitReachedBellmanLoss Q hQ C.rule C.measurable_rule hw hct
  have heq : (fun z : Instance.FirstFutureData i ↦ π.reachedBellmanLoss P w c p.1
      (insertCandidate i (p.2.2, z.1)) (Instance.firstChildClocks i (p.2.1, z.2))) =ᵐ[P.firstFutureLaw i]
      (fun z ↦ π.bellmanActionLoss P i w c p + if π.firstAction p.1 i p.2.1 p.2.2 = true then 0 else
        (π.fixedContinuation (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)).reachedBellmanLoss
          Q w (c * (1 - p.2.1)) () z.1 z.2) := by
    filter_upwards [P.firstFuture_clocks_positive i] with z hz
    exact π.reachedBellmanLoss_firstStep P hP hw hc p.1 i ht p.2.2 z.1 z.2 hz
  rw [integral_congr_ae heq]
  by_cases ha : π.firstAction p.1 i p.2.1 p.2.2 = true
  · simp only [ha, if_true]
    simp
  · simp only [ha, Bool.false_eq_true, if_false]
    rw [integral_add (integrable_const _) hInt]
    simp only [integral_const, probReal_univ, one_smul]
    rw [← hChild]

/-- The finite performance-difference identity: true scalar regret is exactly
the expected sum of Bellman action losses at every reached arrival, for any
admissible randomized history-dependent competing policy. -/
theorem RandomizedPolicy.bellman_performanceDifference {m : ℕ} (π : RandomizedPolicy m)
    (P : Instance m) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue P w c - π.scalarObjective P w c = π.expectedReachedBellmanLoss P w c := by
  induction m using Nat.strong_induction_on generalizing w c with
  | h m ih =>
    cases m with
    | zero =>
      rw [optimalScalarValue_empty P w c, π.empty_scalarObjective P w c, sub_self]
      simp [RandomizedPolicy.expectedReachedBellmanLoss, Policy.reachedBellmanLoss]
    | succ n =>
      rw [π.bellman_firstLossIdentity P hP hw hc]
      unfold RandomizedPolicy.expectedReachedBellmanLoss
      rw [P.integral_firstStepWorld_iterated π.seedLaw
        (f := fun ω : π.World ↦ π.rule.reachedBellmanLoss P w c ω.2.2 ω.1 ω.2.1)
        (π.rule.measurable_reachedBellmanLoss π.measurable_rule P hP hw hc
          (measurable_snd.comp measurable_snd) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
          (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)))
        (π.rule.integrable_reachedBellmanLoss π.measurable_rule P hP π.seedLaw hw hc)]
      apply Finset.sum_congr rfl
      intro i _hi
      apply integral_congr_ae
      filter_upwards [(P.firstPrefix_time_measurePreserving π.seedLaw i).quasiMeasurePreserving.ae
        (Instance.firstChildTimeLaw_mem_unitInterval i)] with p hp
      let Q := P.restrictTo (remainingSet i)
      let C := π.rule.fixedContinuationPolicy π.measurable_rule (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)
      have hQ := P.restrictTo_integrable_maximum (remainingSet i) hP
      have hct := mul_nonneg hc (sub_nonneg.mpr hp.1.2)
      have hchild := ih (remainingSet i).card (remainingSet_card_lt i) C Q hQ hw hct
      have hreg : π.rule.bellmanChildRegret P i w c p = C.expectedReachedBellmanLoss Q w (c * (1 - p.2.1)) := by
        unfold Policy.bellmanChildRegret Instance.bellmanContinuation
        rw [max_eq_right (sub_nonneg.mpr hp.1.2), π.rule.firstContinuationObjective_eq π.measurable_rule P i w c p]
        exact hchild
      rw [hreg]
      exact (π.rule.expectedReachedLoss_firstStep π.measurable_rule P hP hw hc p i hp.2).symm

end ProphetSecretary.Model
