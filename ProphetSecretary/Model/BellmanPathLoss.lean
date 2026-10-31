import ProphetSecretary.Model.BellmanLoss

/-!
# Reached Bellman losses on complete executions

Each action uses its actual observed past. The value used to assess its loss is
the scalar continuation of the unseen original identities. The complete vector
serves only to evaluate the analytical sum of reached losses.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

noncomputable def Instance.continuationAtArrival (P : Instance n) (w c : ℝ)
    (x u : Fin n → ℝ) (i : Fin n) : ℝ :=
  P.continuationValue ((unseen (history Finset.univ x u (u i))).erase i) (max 0 (1 - u i)) w c

lemma Instance.continuationAtArrival_eq_threshold (P : Instance n) {w : ℝ} (hw : 0 < w)
    (c : ℝ) (x u : Fin n → ℝ) (i : Fin n) :
    P.continuationAtArrival w c x u i =
      w * P.valueThreshold w c (unseen (history Finset.univ x u (u i))) (u i) i := by
  unfold Instance.continuationAtArrival Instance.valueThreshold
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hw.ne']

noncomputable def Policy.arrivalBellmanLoss (π : Policy Seed n) (P : Instance n)
    (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) (i : Fin n) : ℝ :=
  max (w * x i) (P.continuationAtArrival w c x u i) -
    if π.action r Finset.univ x u i = true then w * x i else P.continuationAtArrival w c x u i

noncomputable def Policy.reachedBellmanLoss (π : Policy Seed n) (P : Instance n)
    (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if π.Reaches r x u i then π.arrivalBellmanLoss P w c r x u i else 0

lemma Policy.arrivalBellmanLoss_nonnegative (π : Policy Seed n) (P : Instance n)
    (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) (i : Fin n) :
    0 ≤ π.arrivalBellmanLoss P w c r x u i := by
  unfold Policy.arrivalBellmanLoss
  split_ifs
  · exact sub_nonneg.mpr (le_max_left _ _)
  · exact sub_nonneg.mpr (le_max_right _ _)

lemma Policy.reachedBellmanLoss_nonnegative (π : Policy Seed n) (P : Instance n)
    (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) : 0 ≤ π.reachedBellmanLoss P w c r x u := by
  apply Finset.sum_nonneg
  intro i _hi
  split_ifs
  · exact π.arrivalBellmanLoss_nonnegative P w c r x u i
  · exact le_rfl

lemma Instance.valueThreshold_extend (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (y v : Fin A.card → ℝ) (j : Fin A.card) (hv : 0 < v j) :
    P.valueThreshold w c
      (unseen (history Finset.univ (extendValues A H y) (extendClocks A s H v)
        (extendClocks A s H v (stateEmbedding A j))))
      (extendClocks A s H v (stateEmbedding A j)) (stateEmbedding A j) =
      (P.restrictTo A).valueThreshold w (c * (1 - s))
        (unseen (history Finset.univ y v (v j))) (v j) j := by
  rw [extendClocks_stateEmbedding, ← continuationHistory_history A hs H hH y v hv,
    unseen_continuationHistory A s H hH, P.valueThreshold_after_elapsed _ _ _ _ _ _ hs.le]
  exact (P.valueThreshold_restrictBy (A.orderEmbOfFin rfl)
    (unseen (history Finset.univ y v (v j))) j hP hw
    (mul_nonneg hc (sub_nonneg.mpr hs.le)) (v j)).symm

lemma Policy.arrivalBellmanLoss_extend (π : Policy Seed n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (r : Seed)
    (y v : Fin A.card → ℝ) (j : Fin A.card) (hv : 0 < v j) :
    π.arrivalBellmanLoss P w c r (extendValues A H y) (extendClocks A s H v) (stateEmbedding A j) =
      (π.fixedContinuation A r s H).arrivalBellmanLoss (P.restrictTo A) w (c * (1 - s)) () y v j := by
  have hvalue : P.continuationAtArrival w c (extendValues A H y) (extendClocks A s H v) (stateEmbedding A j) =
      (P.restrictTo A).continuationAtArrival w (c * (1 - s)) y v j := by
    rw [P.continuationAtArrival_eq_threshold hw,
      (P.restrictTo A).continuationAtArrival_eq_threshold hw]
    exact congrArg (w * ·) (P.valueThreshold_extend hP A hs H hH hw.le hc y v j hv)
  have hact : π.action r Finset.univ (extendValues A H y) (extendClocks A s H v) (stateEmbedding A j) =
      (π.fixedContinuation A r s H).action () Finset.univ y v j :=
    (π.continuationRule_action A hs H hH r y v j hv).symm
  simp only [Policy.arrivalBellmanLoss, extendValues_stateEmbedding, hvalue, hact]

lemma Policy.reaches_extend (π : Policy Seed n) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    (r : Seed) (y v : Fin A.card → ℝ) (hv : ∀ j, 0 < v j)
    (hReject : PrefixRejected π r A H) (j : Fin A.card) :
    π.Reaches r (extendValues A H y) (extendClocks A s H v) (stateEmbedding A j) ↔
      (π.fixedContinuation A r s H).Reaches () y v j := by
  unfold Policy.Reaches
  rw [extendClocks_stateEmbedding, π.stoppingTime_extend A hs H hH r y v hv hReject]
  exact (add_le_add_iff_left s).trans (mul_le_mul_iff_right₀ (sub_pos.mpr hs))

lemma Policy.reaches_firstChild (π : Policy Seed (n + 1)) (r : Seed) (i : Fin (n + 1))
    {t : ℝ} (ht : t < 1) (x : ℝ) (y v : Fin (remainingSet i).card → ℝ)
    (hv : ∀ j, 0 < v j) :
    π.Reaches r (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) i := by
  unfold Policy.Reaches
  rw [firstChildClocks_same]
  apply (π.le_stoppingTime_iff _ _ _ _ _).mpr
  refine ⟨ht.le, ?_⟩
  intro j _hj
  by_cases hji : j = i
  · simpa only [hji, firstChildClocks_same] using (le_rfl : t ≤ t)
  · exact (firstChildClocks_gt_of_ne i j ht v hv hji).le

lemma Policy.arrivalBellmanLoss_first (π : Policy Seed (n + 1)) (P : Instance (n + 1))
    (r : Seed) (i : Fin (n + 1)) {t : ℝ} (ht : t < 1) (x : ℝ)
    (y v : Fin (remainingSet i).card → ℝ) (hv : ∀ j, 0 < v j) (w c : ℝ) :
    π.arrivalBellmanLoss P w c r (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) i =
      π.bellmanActionLoss P i w c (r, t, x) := by
  have hV : P.continuationAtArrival w c (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) i =
      P.bellmanContinuation i w c t := by
    unfold Instance.continuationAtArrival
    rw [firstChildClocks_same, history_firstChildClocks i ht x y v hv]
    have hu : unseen (fun _ : Fin (n + 1) ↦ (none : Option (ℝ × ℝ))) = Finset.univ := by
      ext j
      simp [unseen]
    rw [hu]
    rfl
  simp only [Policy.arrivalBellmanLoss, Policy.bellmanActionLoss, insertCandidate_same, hV,
    π.action_firstChild r i ht x y v hv]

/-- Complete pathwise recursion for the sum of reached Bellman losses. An
accepted first offer stops the sum; a rejected first offer transports every
later reached action and its original-label continuation exactly to the child. -/
lemma Policy.reachedBellmanLoss_firstStep (π : Policy Seed (n + 1)) (P : Instance (n + 1))
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (r : Seed) (i : Fin (n + 1)) {t : ℝ} (ht : t < 1) (x : ℝ)
    (y v : Fin (remainingSet i).card → ℝ) (hv : ∀ j, 0 < v j) :
    π.reachedBellmanLoss P w c r (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) =
      π.bellmanActionLoss P i w c (r, t, x) +
        if π.firstAction r i t x = true then 0 else
          (π.fixedContinuation (remainingSet i) r t (firstPrefix i t x)).reachedBellmanLoss
            (P.restrictTo (remainingSet i)) w (c * (1 - t)) () y v := by
  let F := fun j : Fin (n + 1) ↦
    if π.Reaches r (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) j then
      π.arrivalBellmanLoss P w c r (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) j else 0
  have hfirst : F i = π.bellmanActionLoss P i w c (r, t, x) := by
    dsimp [F]
    rw [if_pos (π.reaches_firstChild r i ht x y v hv), π.arrivalBellmanLoss_first P r i ht x y v hv w c]
  change (∑ j, F j) = _
  rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ i), hfirst]
  apply congrArg (π.bellmanActionLoss P i w c (r, t, x) + ·)
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
    unfold Policy.reachedBellmanLoss
    apply Finset.sum_congr rfl
    intro j _hj
    have hreach := π.reaches_extend (remainingSet i) ht (firstPrefix i t x) hH r y v hv hReject j
    have hloss := π.arrivalBellmanLoss_extend P hP (remainingSet i) ht (firstPrefix i t x) hH hw hc r y v j (hv j)
    rw [extendValues_firstPrefix, extendClocks_firstPrefix] at hreach hloss
    dsimp [F]
    rw [hreach, hloss]

end ProphetSecretary.Model
