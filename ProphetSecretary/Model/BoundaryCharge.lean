import ProphetSecretary.Model.BoundaryDecomposition

/-!
# Identification of a branch coefficient with its selection charge

The pending execution and the policy design are fixed at the base duration
coefficient. The candidate's complete value enters only the analytical root.
-/

open MeasureTheory Set Filter
open scoped Topology
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.branchMultiplier_root_iff (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (ω : World n Unit) (A : Finset (Fin n))
    (hx : optimalScalarValue (P.restrictTo A) 1 0 < ω.1 i)
    (hr0 : (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (ω.1 i) ≠ 0) :
    let r := (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (ω.1 i)
    (r ∈ Icc (0 : ℝ) 1 ∧ otherUnseen ω.2.1 i r = A ∧
        r ≤ (P.valuePolicy hP zero_le_one hz.le).rule.pendingTime () ω.1 ω.2.1 i) ↔
      P.InteriorCrossing hP i z (ω.1 i) A ω.2.1 ∧
        r ≤ (P.valuePolicy hP zero_le_one hz.le).rule.pendingTime () ω.1 ω.2.1 i := by
  dsimp only
  constructor
  · rintro ⟨hr, hA, hσ⟩
    have hrpos := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    have hd : (P.restrictTo A).durationRoot (P.restrictTo_integrable_maximum A hP) (ω.1 i) < z := by
      apply (div_lt_one hz).mp
      change (P.restrictTo A).durationRoot (P.restrictTo_integrable_maximum A hP) (ω.1 i) / z < 1
      dsimp only [Instance.crossingTime] at hrpos
      linarith
    exact ⟨⟨by rw [← hA]; exact otherUnseen_not_mem _ _ _, hx, hd, hA⟩, hσ⟩
  · rintro ⟨hK, hσ⟩
    exact ⟨⟨(hK.time_mem_Ioo P hP hz).1.le, (hK.time_mem_Ioo P hP hz).2.le⟩, hK.2.2.2, hσ⟩

lemma Instance.branchCoefficient_eq_charge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (ω : World n Unit) (A : Finset (Fin n))
    (hx : optimalScalarValue (P.restrictTo A) 1 0 < ω.1 i)
    (hr0 : (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (ω.1 i) ≠ 0) :
    let Q := P.restrictTo A
    let hQ := P.restrictTo_integrable_maximum A hP
    let r := Q.crossingTime hQ z (ω.1 i)
    let d := Q.durationRoot hQ (ω.1 i)
    (P.valuePolicy hP zero_le_one hz.le).rule.branchMultiplier () ω.1 ω.2.1 i A r * d ^ 2 *
      Q.rootDuration hQ (ω.1 i) / (2 * z ^ 3) =
      P.crossingSelectionCharge hP i hz (ω.1 i) A ω / (2 * z) := by
  dsimp only
  let π : Policy Unit n := (P.valuePolicy hP zero_le_one hz.le).rule
  let Q := P.restrictTo A
  let hQ := P.restrictTo_integrable_maximum A hP
  let r := Q.crossingTime hQ z (ω.1 i)
  let d := Q.durationRoot hQ (ω.1 i)
  let T := Q.rootDuration hQ (ω.1 i)
  change (if r ∈ Icc (0 : ℝ) 1 ∧ otherUnseen ω.2.1 i r = A ∧ r ≤ π.pendingTime () ω.1 ω.2.1 i then 1 else 0) *
      d ^ 2 * T / (2 * z ^ 3) =
    (if P.InteriorCrossing hP i z (ω.1 i) A ω.2.1 ∧ r ≤ π.pendingTime () ω.1 ω.2.1 i then
      (1 - r) ^ 2 * T else 0) / (2 * z)
  have hi : (r ∈ Icc (0 : ℝ) 1 ∧ otherUnseen ω.2.1 i r = A ∧ r ≤ π.pendingTime () ω.1 ω.2.1 i) ↔
    P.InteriorCrossing hP i z (ω.1 i) A ω.2.1 ∧ r ≤ π.pendingTime () ω.1 ω.2.1 i :=
      P.branchMultiplier_root_iff hP i hz ω A hx hr0
  simp only [hi]
  split_ifs
  · rw [one_mul]
    dsimp only [r, Instance.crossingTime]
    rw [sub_sub_cancel]
    field_simp [hz.ne']
    dsimp only [d]
    ring
  · simp only [zero_mul, zero_div]

/-- The state-branch quadratic coefficient is precisely its actual selection
charge, scaled by `1/(2z)`. Invalid and below-baseline states vanish. -/
theorem Instance.stateBranch_regret_limit (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (ω : World n Unit) (A : Finset (Fin n))
    (hr0 : (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (ω.1 i) ≠ 0)
    (hru : ∀ j, j ≠ i →
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (ω.1 i) ≠ ω.2.1 j) :
    Tendsto (fun h : ℝ ↦ (∫ t : ℝ,
      (P.valuePolicy hP zero_le_one hz.le).rule.branchMultiplier () ω.1 ω.2.1 i A t *
        P.stateBranchLoss hP A z (z + h) (ω.1 i) t) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (P.crossingSelectionCharge hP i hz (ω.1 i) A ω / (2 * z))) := by
  by_cases hx : optimalScalarValue (P.restrictTo A) 1 0 < ω.1 i
  · have h := P.branch_regret_limit hP (P.valuePolicy hP zero_le_one hz.le).rule ()
      ω.1 ω.2.1 i A hz hx hr0 hru
    dsimp only at h
    rw [P.branchCoefficient_eq_charge hP i hz ω A hx hr0] at h
    simpa only [Instance.stateBranchLoss, if_pos hx] using h
  · have hK : ¬ P.InteriorCrossing hP i z (ω.1 i) A ω.2.1 := fun h ↦ hx h.2.1
    simp only [Instance.stateBranchLoss, if_neg hx, mul_zero, integral_zero, zero_div,
      Instance.crossingSelectionCharge, hK, false_and, if_false]
    exact tendsto_const_nhds

end ProphetSecretary.Model
