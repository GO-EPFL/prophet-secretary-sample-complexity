import ProphetSecretary.Probability.FairSigns
import ProphetSecretary.Model.ProphetWinner

/-! # Fair-sign gain at a tied positive maximum
A fixed old winner proves nonnegative expected gain on every value vector.
Two distinct eligible maximizers give the additional expected gain `h/2`.
The maximum and its tie event remain analytical complete-vector quantities.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

def MaximumTiedAtLeast (b : ℝ) (x : Fin n → ℝ) : Prop :=
  b ≤ Instance.maximum x ∧ ∃ i j, i ≠ j ∧ x i = Instance.maximum x ∧ x j = Instance.maximum x

lemma measurableSet_maximumTiedAtLeast (b : ℝ) : MeasurableSet {x : Fin n → ℝ | MaximumTiedAtLeast b x} := by
  apply (measurableSet_le measurable_const Instance.measurable_maximum).inter
  change MeasurableSet {x : Fin n → ℝ | ∃ i j : Fin n, i ≠ j ∧ x i = Instance.maximum x ∧ x j = Instance.maximum x}
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simpa only [hij, ne_eq, not_false_eq_true, true_and, Set.setOf_and] using
      (measurableSet_eq_fun (measurable_pi_apply i) Instance.measurable_maximum).inter
        (measurableSet_eq_fun (measurable_pi_apply j) Instance.measurable_maximum)

noncomputable def highSignPerturbation (h : ℝ) (σ : Fin n → Bool) (i : Fin n) (x : ℝ) : ℝ :=
  if 2 * h ≤ x then variableSign σ i else 0

lemma highSignPerturbation_measurable (h : ℝ) (σ : Fin n → Bool) (i : Fin n) :
    Measurable (highSignPerturbation h σ i) :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

lemma highSignPerturbation_bound (h : ℝ) (σ : Fin n → Bool) (i : Fin n) (x : ℝ) :
    |highSignPerturbation h σ i x| ≤ 1 := by
  unfold highSignPerturbation
  split_ifs
  · exact (abs_variableSign σ i).le
  · norm_num

lemma highSignPerturbation_support (h : ℝ) (σ : Fin n → Bool) (i : Fin n) (x : ℝ) (hx : x < 2 * h) :
    highSignPerturbation h σ i x = 0 := if_neg (not_le.mpr hx)

lemma highSignPerturbation_reverse (h : ℝ) (σ : Fin n → Bool) :
    highSignPerturbation h (reverseSigns σ) = fun i x ↦ -highSignPerturbation h σ i x := by
  funext i x
  unfold highSignPerturbation
  split_ifs <;> simp only [variableSign_reverse, neg_zero]

@[simp] lemma integral_highSignPerturbation (h : ℝ) (i : Fin n) (x : ℝ) :
    (∫ σ, highSignPerturbation h σ i x ∂fairSigns n) = 0 := by
  by_cases hx : 2 * h ≤ x
  · simpa only [highSignPerturbation, if_pos hx] using integral_variableSign i
  · simp only [highSignPerturbation, if_neg hx, integral_zero]

noncomputable def signedMaximum (h : ℝ) (x : Fin n → ℝ) (σ : Fin n → Bool) : ℝ :=
  Instance.maximum (fun i ↦ x i + h * highSignPerturbation h σ i (x i))

lemma mean_signedMaximum_ge (h : ℝ) (x : Fin n → ℝ) :
    Instance.maximum x ≤ ∫ σ, signedMaximum h x σ ∂fairSigns n := by
  by_cases hx : 0 < Instance.maximum x
  · obtain ⟨i, hi⟩ := exists_prophetWins hx
    have hPt (σ : Fin n → Bool) : Instance.maximum x + h * highSignPerturbation h σ i (x i) ≤ signedMaximum h x σ := by
      rw [← hi.2.1]
      exact Instance.le_maximum (fun j ↦ x j + h * highSignPerturbation h σ j (x j)) i
    have hI := integral_mono (fairSigns_integrable _) (fairSigns_integrable _) hPt
    rw [integral_add (f := fun _ : Fin n → Bool ↦ Instance.maximum x)
      (g := fun σ ↦ h * highSignPerturbation h σ i (x i)) (integrable_const _)
      ((fairSigns_integrable _).const_mul h), integral_const_mul, integral_highSignPerturbation] at hI
    simpa only [integral_const, probReal_univ, one_smul, mul_zero, add_zero] using hI
  · have hz : Instance.maximum x = 0 := le_antisymm (not_lt.mp hx) (Instance.maximum_nonnegative x)
    rw [hz]
    exact integral_nonneg (fun σ ↦ Instance.maximum_nonnegative _)

lemma mean_signedMaximum_ge_of_tied {h : ℝ} (_hh : 0 ≤ h) (x : Fin n → ℝ)
    (hTie : MaximumTiedAtLeast (2 * h) x) :
    Instance.maximum x + h / 2 ≤ ∫ σ, signedMaximum h x σ ∂fairSigns n := by
  obtain ⟨hLevel, i, j, hij, hi, hj⟩ := hTie
  have hPt (σ : Fin n → Bool) : Instance.maximum x + h * max (variableSign σ i) (variableSign σ j) ≤ signedMaximum h x σ := by
    have hI : Instance.maximum x + h * variableSign σ i ≤ signedMaximum h x σ := by
      have he : highSignPerturbation h σ i (x i) = variableSign σ i := if_pos (by rw [hi]; exact hLevel)
      have hv := Instance.le_maximum (fun k ↦ x k + h * highSignPerturbation h σ k (x k)) i
      rw [he, hi] at hv
      exact hv
    have hJ : Instance.maximum x + h * variableSign σ j ≤ signedMaximum h x σ := by
      have he : highSignPerturbation h σ j (x j) = variableSign σ j := if_pos (by rw [hj]; exact hLevel)
      have hv := Instance.le_maximum (fun k ↦ x k + h * highSignPerturbation h σ k (x k)) j
      rw [he, hj] at hv
      exact hv
    by_cases hsign : variableSign σ i ≤ variableSign σ j
    · rw [max_eq_right hsign]
      exact hJ
    · rw [max_eq_left (le_of_not_ge hsign)]
      exact hI
  have hI := integral_mono (fairSigns_integrable _) (fairSigns_integrable _) hPt
  rw [integral_add (f := fun _ : Fin n → Bool ↦ Instance.maximum x)
    (g := fun σ ↦ h * max (variableSign σ i) (variableSign σ j)) (integrable_const _)
    ((fairSigns_integrable _).const_mul h), integral_const_mul, integral_max_variableSigns hij] at hI
  simpa only [integral_const, probReal_univ, one_smul, div_eq_mul_inv, one_mul] using hI

theorem mean_signedMaximum_tie_gain {h : ℝ} (hh : 0 ≤ h) (x : Fin n → ℝ) :
    Instance.maximum x + (h / 2) * (if MaximumTiedAtLeast (2 * h) x then 1 else 0) ≤
      ∫ σ, signedMaximum h x σ ∂fairSigns n := by
  by_cases hTie : MaximumTiedAtLeast (2 * h) x
  · simpa only [if_pos hTie, mul_one] using mean_signedMaximum_ge_of_tied hh x hTie
  · simpa only [if_neg hTie, mul_zero, add_zero] using mean_signedMaximum_ge h x

end ProphetSecretary.Model
