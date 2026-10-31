import ProphetSecretary.Model.LawStateBranches
import ProphetSecretary.Model.LawConditionalRegret

/-!
# Finite clock-integral decomposition into actual unseen states

Every branch is supported on the physical unit clock interval. Its multiplier
records the old pending execution and the identities not yet revealed. The
finite sum reconstructs the actual reached Bellman loss except at null terminal
timestamps, where the model retains its explicit stopping convention.
-/

open MeasureTheory Set Filter
open scoped Classical Topology BigOperators

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ} {Seed : Type*}

lemma Policy.branchMultiplier_mem_unit (π : Policy Seed n) (r : Seed) (x u : Fin n → ℝ)
    (i : Fin n) (A : Finset (Fin n)) (t : ℝ) : π.branchMultiplier r x u i A t ∈ Icc (0 : ℝ) 1 := by
  unfold Policy.branchMultiplier
  split_ifs <;> norm_num

lemma Policy.branchMultiplier_zero_off_unit (π : Policy Seed n) (r : Seed) (x u : Fin n → ℝ)
    (i : Fin n) (A : Finset (Fin n)) {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) : π.branchMultiplier r x u i A t = 0 := by
  unfold Policy.branchMultiplier
  rw [if_neg (fun h ↦ ht h.1)]

lemma Policy.measurable_branchMultiplier (π : Policy Seed n) (r : Seed) (x u : Fin n → ℝ)
    (i : Fin n) (A : Finset (Fin n)) : Measurable (π.branchMultiplier r x u i A) := by
  have hA : MeasurableSet {t : ℝ | otherUnseen u i t = A} :=
    measurableSet_eq_fun (measurable_otherUnseen u i) measurable_const
  have hReach : MeasurableSet {t : ℝ | t ≤ π.pendingTime r x u i} := measurableSet_le measurable_id measurable_const
  exact Measurable.ite (measurableSet_Icc.inter (hA.inter hReach)) measurable_const measurable_const

noncomputable def Instance.lawStateBranchLoss (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) (A : Finset (Fin n)) (ω : World n Unit) (t : ℝ) : ℝ :=
  let Q := P.likelihoodWidePath h hh hb hm θ
  let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  (Q.valuePolicy hQ hw.le hc).rule.branchMultiplier () ω.1 ω.2.1 i A t *
    ProphetSecretary.Analysis.rootActionLoss (P.lawStateValue h hh hb hm w ρ A) (w * ω.1 i) c
      (P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i)) t

lemma Instance.lawStateBranchLoss_nonnegative (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) (A : Finset (Fin n)) (ω : World n Unit) (t : ℝ) :
    0 ≤ P.lawStateBranchLoss hw hc hbound h hh hb hm θ ρ i A ω t :=
  mul_nonneg (Policy.branchMultiplier_mem_unit _ _ _ _ _ _ _).1
    (ProphetSecretary.Analysis.rootActionLoss_nonnegative _ _ _ _ _)

lemma Instance.lawStateValue_continuous (P : Instance n) {w H : ℝ}
    (hw : 0 ≤ w) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (ρ : ℝ) (A : Finset (Fin n)) : Continuous (P.lawStateValue h hh hb hm w ρ A) := by
  let Q := (P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) ρ
  have hQB := (P.restrictTo A).likelihoodWidePath_bounded (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) ρ
    (fun j ↦ hbound (stateEmbedding A j))
  exact Q.weightedSaturatedValue_continuous (Q.integrable_maximum_of_bounded hQB) hw

lemma Instance.measurable_lawStateBranchLoss (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) (A : Finset (Fin n)) (ω : World n Unit) :
    Measurable (P.lawStateBranchLoss hw hc hbound h hh hb hm θ ρ i A ω) :=
  (Policy.measurable_branchMultiplier _ _ _ _ _ _).mul
    (ProphetSecretary.Analysis.measurable_rootActionLoss (P.lawStateValue_continuous hw.le hbound h hh hb hm ρ A).measurable _ _ _)

lemma Instance.lawStateValue_unit_bound (P : Instance n) {w c H : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (ρ : ℝ) (A : Finset (Fin n)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    P.lawStateValue h hh hb hm w ρ A (c * (1 - t)) ∈ Icc (0 : ℝ) (w * H + c) := by
  let Q := (P.likelihoodWidePath h hh hb hm ρ).restrictTo A
  have hQB (j : Fin A.card) : ∀ᵐ a ∂Q.law j, a ≤ H :=
    P.likelihoodWidePath_bounded h hh hb hm ρ hbound (stateEmbedding A j)
  have hQ := Q.integrable_maximum_of_bounded hQB
  rw [P.lawStateValue_eq_instanceValue h hh hb hm w ρ A]
  have hcoef0 : 0 ≤ c * (1 - t) := mul_nonneg hc (sub_nonneg.mpr ht.2)
  rw [max_eq_right hcoef0]
  refine ⟨optimalScalarValue_nonnegative Q hQ hw hcoef0, ?_⟩
  have hMax := Q.expectedMaximum_le_of_bounded hH hQB
  have hV := optimalScalarValue_le_benchmark Q hQ hw hcoef0
  have hCost : c * (1 - t) ≤ c := by nlinarith [mul_nonneg hc ht.1]
  nlinarith [mul_le_mul_of_nonneg_left hMax hw]

lemma Instance.integrable_lawStateBranchLoss (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) (A : Finset (Fin n)) (ω : World n Unit) :
    Integrable (P.lawStateBranchLoss hw hc hbound h hh hb hm θ ρ i A ω) volume := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc).rule
  have hOn : IntegrableOn (P.lawStateBranchLoss hw hc hbound h hh hb hm θ ρ i A ω) (Icc (0 : ℝ) 1) volume := by
    change Integrable (P.lawStateBranchLoss hw hc hbound h hh hb hm θ ρ i A ω) Instance.uniformClock
    apply Integrable.of_bound (P.measurable_lawStateBranchLoss hw hc hbound h hh hb hm θ ρ i A ω).aestronglyMeasurable
      (|w * ω.1 i| + (w * H + c))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (P.lawStateBranchLoss_nonnegative hw hc hbound h hh hb hm θ ρ i A ω t)]
    have hm0 := π.branchMultiplier_mem_unit () ω.1 ω.2.1 i A t
    have hLoss0 := ProphetSecretary.Analysis.rootActionLoss_nonnegative (P.lawStateValue h hh hb hm w ρ A) (w * ω.1 i) c
      (P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i)) t
    have hLoss := ProphetSecretary.Analysis.rootActionLoss_le_abs (P.lawStateValue h hh hb hm w ρ A) (w * ω.1 i) c
      (P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i)) t
    have hNew := P.lawStateValue_unit_bound hw.le hc hH hbound h hh hb hm ρ A ht
    rw [abs_of_nonneg hNew.1] at hLoss
    change π.branchMultiplier () ω.1 ω.2.1 i A t * _ ≤ _
    have hMul := mul_le_mul_of_nonneg_right hm0.2 hLoss0
    rw [one_mul] at hMul
    exact hMul.trans (hLoss.trans (add_le_add le_rfl hNew.2))
  apply hOn.integrable_of_forall_notMem_eq_zero
  intro t ht
  change π.branchMultiplier () ω.1 ω.2.1 i A t * _ = 0
  rw [π.branchMultiplier_zero_off_unit () ω.1 ω.2.1 i A ht, zero_mul]

lemma Instance.lawClockLoss_eq_sum_stateBranches (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) (ω : World n Unit) {t : ℝ} (ht : t < 1) :
    let Q := P.likelihoodWidePath h hh hb hm θ
    let T := P.likelihoodWidePath h hh hb hm ρ
    let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
    let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc.le).rule
    (if t ∈ Icc (0 : ℝ) 1 ∧ t ≤ π.pendingTime () ω.1 ω.2.1 i then
      π.arrivalBellmanLoss T w c () ω.1 (Function.update ω.2.1 i t) i else 0) =
      ∑ A : Finset (Fin n), P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ ρ i A ω t := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc.le).rule
  rw [Finset.sum_eq_single (otherUnseen ω.2.1 i t)]
  · have hBranch := P.lawPolicy_arrivalLoss_eq_stateBranch hw hc hbound h hh hb hm θ ρ ω.1 ω.2.1 i ht (otherUnseen ω.2.1 i t) rfl
    change (if t ∈ Icc (0 : ℝ) 1 ∧ t ≤ π.pendingTime () ω.1 ω.2.1 i then
        π.arrivalBellmanLoss T w c () ω.1 (Function.update ω.2.1 i t) i else 0) =
      π.branchMultiplier () ω.1 ω.2.1 i (otherUnseen ω.2.1 i t) t * _
    rw [Policy.branchMultiplier]
    by_cases hU : t ∈ Icc (0 : ℝ) 1
    · by_cases hR : t ≤ π.pendingTime () ω.1 ω.2.1 i
      · simp only [hU, hR, and_self, if_true, one_mul]
        exact hBranch
      · simp only [hR, and_false, if_false, zero_mul]
    · simp only [hU, false_and, if_false, zero_mul]
  · intro A _ hA
    have hnot : otherUnseen ω.2.1 i t ≠ A := Ne.symm hA
    change π.branchMultiplier () ω.1 ω.2.1 i A t * _ = 0
    simp only [Policy.branchMultiplier, hnot, false_and, and_false, if_false, zero_mul]
  · simp

/-- Exact conditional clock integral as a finite sum over actual unseen
identity sets. The only omitted timestamp is the null endpoint one. -/
theorem Instance.lawConditionalRegret_eq_sum_stateBranchIntegrals (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) (ω : World n Unit) :
    P.lawConditionalRegret hw hc.le hbound h hh hb hm θ ρ i ω =
      ∑ A : Finset (Fin n), ∫ t : ℝ, P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ ρ i A ω t := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc.le).rule
  change π.clockConditionalBellmanLoss T w c i ω = _
  rw [π.clockConditionalBellmanLoss_eq_pending T w c i ω]
  unfold Instance.uniformClock
  rw [← integral_indicator measurableSet_Icc]
  calc
    _ = ∫ t : ℝ, ∑ A : Finset (Fin n), P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ ρ i A ω t := by
      apply integral_congr_ae
      filter_upwards [volume.ae_ne (1 : ℝ)] with t hne
      by_cases hU : t ∈ Icc (0 : ℝ) 1
      · rw [Set.indicator_of_mem (s := Icc (0 : ℝ) 1) hU]
        have ht : t < 1 := lt_of_le_of_ne hU.2 hne
        have hp := P.lawClockLoss_eq_sum_stateBranches hw hc hbound h hh hb hm θ ρ i ω ht
        change (if t ≤ π.pendingTime () ω.1 ω.2.1 i then
          π.arrivalBellmanLoss T w c () ω.1 (Function.update ω.2.1 i t) i else 0) = _
        simpa only [hU, true_and] using hp
      · rw [Set.indicator_of_notMem (s := Icc (0 : ℝ) 1) hU]
        apply Eq.symm
        apply Finset.sum_eq_zero
        intro A _
        change π.branchMultiplier () ω.1 ω.2.1 i A t * _ = 0
        rw [π.branchMultiplier_zero_off_unit () ω.1 ω.2.1 i A hU, zero_mul]
    _ = _ := integral_finsetSum Finset.univ (fun A _ ↦ P.integrable_lawStateBranchLoss hw hc.le hH hbound h hh hb hm θ ρ i A ω)

end ProphetSecretary.Model
