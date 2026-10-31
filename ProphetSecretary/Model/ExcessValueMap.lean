import ProphetSecretary.Model.ValueTransform

/-!
# Excess offers above a fixed terminal reward

On nonnegative offers this map is (x−a)₊. Its continuous totalization is the
identity below zero, so its displacement is globally at most a. This allows the
proved noninjective mapped-reward comparison to apply without an unjustified
global bound for the raw positive-part expression on negative inputs.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

noncomputable def excessValueMap (a x : ℝ) : ℝ := x - min a (max x 0)

lemma measurable_excessValueMap (a : ℝ) : Measurable (excessValueMap a) := by
  unfold excessValueMap
  fun_prop

lemma excessValueMap_displacement {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : |excessValueMap a x - x| ≤ a := by
  have hnn : 0 ≤ min a (max x 0) := le_min ha (le_max_right _ _)
  have hle : min a (max x 0) ≤ a := min_le_left _ _
  have heq : excessValueMap a x - x = -(min a (max x 0)) := by unfold excessValueMap; ring
  rw [heq, abs_neg, abs_of_nonneg hnn]
  exact hle

lemma excessValueMap_eq_positivePart {a x : ℝ} (hx : 0 ≤ x) :
    excessValueMap a x = max (x - a) 0 := by
  unfold excessValueMap
  rw [max_eq_left hx]
  by_cases hax : a ≤ x
  · rw [min_eq_left hax, max_eq_left (sub_nonneg.mpr hax)]
  · rw [min_eq_right (not_le.mp hax).le, sub_self, max_eq_right (sub_nonpos.mpr (not_le.mp hax).le)]

lemma excessValueMap_nonnegative {a x : ℝ} (hx : 0 ≤ x) : 0 ≤ excessValueMap a x := by
  rw [excessValueMap_eq_positivePart hx]
  exact le_max_right _ _

lemma excessValueMap_zero {a : ℝ} (ha : 0 ≤ a) : excessValueMap a 0 = 0 := by
  unfold excessValueMap
  rw [max_self, min_eq_right ha, sub_self]

lemma value_le_terminal_add_excess {a : ℝ} (x : ℝ) : x ≤ a + excessValueMap a x := by
  unfold excessValueMap
  linarith only [min_le_left a (max x 0)]

lemma positive_excess_reconstructs_value {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < excessValueMap a x) :
    x = a + excessValueMap a x := by
  have hnn : 0 ≤ min a (max x 0) := le_min ha (le_max_right _ _)
  have hxp : 0 < x := by unfold excessValueMap at hx; linarith
  have hax : a ≤ x := by
    by_contra hn
    unfold excessValueMap at hx
    rw [max_eq_left hxp.le, min_eq_right (not_le.mp hn).le, sub_self] at hx
    exact (lt_irrefl 0) hx
  unfold excessValueMap
  rw [max_eq_left hxp.le, min_eq_left hax]
  ring

variable {n : ℕ}

noncomputable def Instance.excessOffers (P : Instance n) (a : ℝ) : Instance n :=
  P.mapValues (fun _ => excessValueMap a) (fun _ => measurable_excessValueMap a)
    (fun i => (P.nonnegative i).mono fun _ hx => excessValueMap_nonnegative hx)

lemma Instance.excessOffers_integrable_maximum (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a : ℝ} (ha : 0 ≤ a) :
    Integrable Instance.maximum (P.excessOffers a).valuesLaw :=
  P.mapValues_integrable_of_bounded_displacement hP _ _ _
    (fun _ => Filter.Eventually.of_forall (excessValueMap_displacement ha))

end ProphetSecretary.Model
