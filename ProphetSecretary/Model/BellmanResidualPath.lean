import ProphetSecretary.Model.BellmanResidualBasic

/-!
# Transporting reached residual sums

The transition discrepancy uses the fixed design and true marginal laws, but its state
is the actual observed unseen set. Restarting after a rejected prefix transports both
laws in the same increasing original-identity enumeration.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma Instance.continuationAtArrival_first (Q : Instance (n + 1)) (w c : ℝ)
    (i : Fin (n + 1)) {t : ℝ} (ht : t < 1) (x : ℝ)
    (y v : Fin (remainingSet i).card → ℝ) (hv : ∀ j, 0 < v j) :
    Q.continuationAtArrival w c (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) i =
      Q.bellmanContinuation i w c t := by
  unfold Instance.continuationAtArrival
  rw [firstChildClocks_same, history_firstChildClocks i ht x y v hv]
  have he : unseen (fun _ : Fin (n + 1) => (none : Option (ℝ × ℝ))) = Finset.univ := by
    ext j
    simp [unseen]
  rw [he]
  rfl

lemma Instance.transitionResidual_first (Q P : Instance (n + 1)) (w c : ℝ)
    (i : Fin (n + 1)) {t : ℝ} (ht : t < 1)
    (v : Fin (remainingSet i).card → ℝ) (hv : ∀ j, 0 < v j) :
    Q.transitionResidual P w c (Instance.firstChildClocks i (t, v)) i = Q.firstTransitionResidual P i w c t := by
  unfold Instance.transitionResidual Instance.firstTransitionResidual
  rw [Q.continuationAtArrival_values_invariant w c (fun _ => 0) (insertCandidate i (0, fun _ => 0))
      (Instance.firstChildClocks i (t, v)) i,
    Q.continuationAtArrival_first w c i ht 0 (fun _ => 0) v hv]

lemma Instance.transitionResidual_extend (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (y v : Fin A.card → ℝ) (j : Fin A.card) (hv : 0 < v j) :
    Q.transitionResidual P w c (extendClocks A s H v) (stateEmbedding A j) =
      (Q.restrictTo A).transitionResidual (P.restrictTo A) w (c * (1 - s)) v j := by
  have hV : Q.continuationAtArrival w c (extendValues A H y) (extendClocks A s H v) (stateEmbedding A j) =
      (Q.restrictTo A).continuationAtArrival w (c * (1 - s)) y v j := by
    rw [Q.continuationAtArrival_eq_threshold hw,
      (Q.restrictTo A).continuationAtArrival_eq_threshold hw]
    exact congrArg (w * ·) (Q.valueThreshold_extend hQ A hs H hH hw.le hc y v j hv)
  have hV0 : Q.continuationAtArrival w c (fun _ => 0) (extendClocks A s H v) (stateEmbedding A j) =
      (Q.restrictTo A).continuationAtArrival w (c * (1 - s)) (fun _ => 0) v j :=
    (Q.continuationAtArrival_values_invariant w c (fun _ => 0) (extendValues A H y) _ _).trans
      (hV.trans ((Q.restrictTo A).continuationAtArrival_values_invariant w (c * (1 - s)) y (fun _ => 0) v j))
  unfold Instance.transitionResidual Instance.lawResidual
  rw [hV0]
  rfl

lemma Policy.reachedTransitionResidual_firstStep (π : Policy Seed (n + 1)) (Q P : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (r : Seed) (i : Fin (n + 1)) {t : ℝ} (ht : t < 1) (x : ℝ)
    (y v : Fin (remainingSet i).card → ℝ) (hv : ∀ j, 0 < v j) :
    π.reachedTransitionResidual Q P w c r (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) =
      Q.firstTransitionResidual P i w c t +
        if π.firstAction r i t x = true then 0 else
          (π.fixedContinuation (remainingSet i) r t (firstPrefix i t x)).reachedTransitionResidual
            (Q.restrictTo (remainingSet i)) (P.restrictTo (remainingSet i)) w (c * (1 - t)) () y v := by
  let F := fun j : Fin (n + 1) =>
    if π.Reaches r (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) j then
      Q.transitionResidual P w c (Instance.firstChildClocks i (t, v)) j else 0
  have hfirst : F i = Q.firstTransitionResidual P i w c t := by
    dsimp [F]
    rw [if_pos (π.reaches_firstChild r i ht x y v hv), Q.transitionResidual_first P w c i ht v hv]
  change (∑ j, F j) = _
  rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ i), hfirst]
  apply congrArg (Q.firstTransitionResidual P i w c t + ·)
  by_cases ha : π.firstAction r i t x = true
  · rw [if_pos ha]
    apply Finset.sum_eq_zero
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hnot : ¬π.Reaches r (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) j := by
      unfold Policy.Reaches
      rw [π.stoppingTime_first_accept r i ht x y v hv ha]
      exact not_le.mpr (firstChildClocks_gt_of_ne i j ht v hv hji)
    exact if_neg hnot
  · rw [if_neg ha]
    have hf : π.firstAction r i t x = false := by cases h : π.firstAction r i t x <;> simp_all
    have hReject := π.prefixRejected_first_reject r i t x hf
    have hH := validPrefix_firstPrefix i t x
    have hmap : Finset.univ.map (stateEmbedding (remainingSet i)) = remainingSet i :=
      (remainingSet i).map_orderEmbOfFin_univ rfl
    change (∑ j ∈ remainingSet i, F j) = _
    rw (occs := .pos [1]) [← hmap]
    rw [Finset.sum_map]
    unfold Policy.reachedTransitionResidual
    apply Finset.sum_congr rfl
    intro j _
    have hreach := π.reaches_extend (remainingSet i) ht (firstPrefix i t x) hH r y v hv hReject j
    have hres := Q.transitionResidual_extend P hQ (remainingSet i) ht (firstPrefix i t x) hH hw hc y v j (hv j)
    rw [extendValues_firstPrefix, extendClocks_firstPrefix] at hreach
    rw [extendClocks_firstPrefix] at hres
    dsimp [F]
    rw [hreach, hres]

/-- The signed transition sum and nonnegative action-loss sum use the same actual
reach events. Neither term changes what the online policy observes. -/
noncomputable def Policy.reachedDesignGap (π : Policy Seed n) (Q P : Instance n)
    (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) : ℝ :=
  π.reachedTransitionResidual Q P w c r x u + π.reachedBellmanLoss Q w c r x u

lemma Policy.reachedDesignGap_eq_sum (π : Policy Seed n) (Q P : Instance n)
    (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) :
    π.reachedDesignGap Q P w c r x u = ∑ i : Fin n, if π.Reaches r x u i then
      Q.transitionResidual P w c u i + π.arrivalBellmanLoss Q w c r x u i else 0 := by
  unfold Policy.reachedDesignGap Policy.reachedTransitionResidual Policy.reachedBellmanLoss
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma Policy.reachedDesignGap_firstStep (π : Policy Seed (n + 1)) (Q P : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (r : Seed) (i : Fin (n + 1)) {t : ℝ} (ht : t < 1) (x : ℝ)
    (y v : Fin (remainingSet i).card → ℝ) (hv : ∀ j, 0 < v j) :
    π.reachedDesignGap Q P w c r (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) =
      (Q.firstTransitionResidual P i w c t + π.bellmanActionLoss Q i w c (r, t, x)) +
        if π.firstAction r i t x = true then 0 else
          (π.fixedContinuation (remainingSet i) r t (firstPrefix i t x)).reachedDesignGap
            (Q.restrictTo (remainingSet i)) (P.restrictTo (remainingSet i)) w (c * (1 - t)) () y v := by
  rw [Policy.reachedDesignGap, π.reachedTransitionResidual_firstStep Q P hQ hw hc r i ht x y v hv,
    π.reachedBellmanLoss_firstStep Q hQ hw hc r i ht x y v hv]
  by_cases ha : π.firstAction r i t x = true
  · simp only [if_pos ha]
    ring
  · simp only [if_neg ha, Policy.reachedDesignGap]
    ring

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]

lemma Policy.measurable_reachedDesignGap (π : Policy Seed n) (hπ : π.IsMeasurable)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ j, Measurable fun ω => x ω j) (hu : ∀ j, Measurable fun ω => u ω j) :
    Measurable (fun ω => π.reachedDesignGap Q P w c (r ω) (x ω) (u ω)) :=
  (π.measurable_reachedTransitionResidual hπ Q P hQ hP hw hc hr hx hu).add
    (π.measurable_reachedBellmanLoss hπ Q hQ hw hc hr hx hu)

lemma Policy.integrable_reachedDesignGap (π : Policy Seed n) (hπ : π.IsMeasurable)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (fun ω : World n Seed => π.reachedDesignGap Q P w c ω.2.2 ω.1 ω.2.1) (P.worldLaw ν) :=
  (π.integrable_reachedTransitionResidual hπ Q P hQ hP ν hw hc).add
    (π.integrable_reachedBellmanLoss_under hπ Q P hQ hP ν hw hc)

noncomputable def RandomizedPolicy.expectedReachedDesignGap (π : RandomizedPolicy n)
    (Q P : Instance n) (w c : ℝ) : ℝ :=
  ∫ ω : π.World, π.rule.reachedDesignGap Q P w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw π.seedLaw

lemma integral_unitReachedDesignGap {m : ℕ} (Q P : Instance m)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (π : Policy Unit m) (hπ : π.IsMeasurable) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ ω : World m Unit, π.reachedDesignGap Q P w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ())) =
      ∫ z : (Fin m → ℝ) × (Fin m → ℝ), π.reachedDesignGap Q P w c () z.1 z.2
        ∂P.valuesLaw.prod (Instance.clocksLaw m) := by
  have hm := π.measurable_reachedDesignGap hπ Q P hQ hP hw hc
    (measurable_snd.comp measurable_snd) (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hp := P.addUnitSeed_measurePreserving
  have h := integral_map (μ := P.valuesLaw.prod (Instance.clocksLaw m)) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h

lemma Policy.expectedReachedDesignGap_firstStep (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (Q P : Instance (n + 1)) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (p : Instance.FirstPrefixData Seed) (i : Fin (n + 1)) (ht : p.2.1 < 1) :
    (∫ z : Instance.FirstFutureData i,
      π.reachedDesignGap Q P w c p.1 (insertCandidate i (p.2.2, z.1))
        (Instance.firstChildClocks i (p.2.1, z.2)) ∂P.firstFutureLaw i) =
      (Q.firstTransitionResidual P i w c p.2.1 + π.bellmanActionLoss Q i w c p) +
        if π.firstAction p.1 i p.2.1 p.2.2 = true then 0 else
          (π.fixedContinuationPolicy hπ (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)).expectedReachedDesignGap
            (Q.restrictTo (remainingSet i)) (P.restrictTo (remainingSet i)) w (c * (1 - p.2.1)) := by
  let D := Q.restrictTo (remainingSet i)
  let T := P.restrictTo (remainingSet i)
  let C := π.fixedContinuationPolicy hπ (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)
  have hD := Q.restrictTo_integrable_maximum (remainingSet i) hQ
  have hT := P.restrictTo_integrable_maximum (remainingSet i) hP
  have hct := mul_nonneg hc (sub_nonneg.mpr ht.le)
  have hInt : Integrable (fun z : Instance.FirstFutureData i =>
      (π.fixedContinuation (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)).reachedDesignGap
        D T w (c * (1 - p.2.1)) () z.1 z.2) (P.firstFutureLaw i) :=
    T.addUnitSeed_measurePreserving.integrable_comp_of_integrable
      (C.rule.integrable_reachedDesignGap C.measurable_rule D T hD hT C.seedLaw hw hct)
  have hChild : C.expectedReachedDesignGap D T w (c * (1 - p.2.1)) =
      ∫ z : Instance.FirstFutureData i,
        (π.fixedContinuation (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)).reachedDesignGap
          D T w (c * (1 - p.2.1)) () z.1 z.2 ∂P.firstFutureLaw i :=
    integral_unitReachedDesignGap D T hD hT C.rule C.measurable_rule hw hct
  have heq : (fun z : Instance.FirstFutureData i => π.reachedDesignGap Q P w c p.1
      (insertCandidate i (p.2.2, z.1)) (Instance.firstChildClocks i (p.2.1, z.2))) =ᵐ[P.firstFutureLaw i]
      (fun z => (Q.firstTransitionResidual P i w c p.2.1 + π.bellmanActionLoss Q i w c p) +
        if π.firstAction p.1 i p.2.1 p.2.2 = true then 0 else
          (π.fixedContinuation (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)).reachedDesignGap
            D T w (c * (1 - p.2.1)) () z.1 z.2) := by
    filter_upwards [P.firstFuture_clocks_positive i] with z hz
    exact π.reachedDesignGap_firstStep Q P hQ hw hc p.1 i ht p.2.2 z.1 z.2 hz
  rw [integral_congr_ae heq]
  by_cases ha : π.firstAction p.1 i p.2.1 p.2.2 = true
  · simp only [ha, if_true]
    simp
  · simp only [ha, Bool.false_eq_true, if_false]
    rw [integral_add (integrable_const _) hInt]
    simp only [integral_const, probReal_univ, one_smul]
    rw [← hChild]

end ProphetSecretary.Model
