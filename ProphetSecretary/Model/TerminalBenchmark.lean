import ProphetSecretary.Model.ExcessValueMap

/-!
# The benchmark with a fixed terminal reward

The expected maximum including a≥0 equals a plus the expected maximum of the
excess offers. The pointwise proof includes the empty instance and negative
inputs of the harmless map totalization; actual offers remain nonnegative.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma maximum_with_terminal_eq_excess {a : ℝ} (ha : 0 ≤ a) (x : Fin n → ℝ) :
    max a (Instance.maximum x) = a + Instance.maximum (fun i => excessValueMap a (x i)) := by
  let y := fun i => excessValueMap a (x i)
  have hY := Instance.maximum_nonnegative y
  have hM : Instance.maximum x ≤ a + Instance.maximum y := by
    apply Instance.maximum_le x (add_nonneg ha hY)
    intro i
    exact (value_le_terminal_add_excess (x i)).trans (add_le_add le_rfl (Instance.le_maximum y i))
  have hL : max a (Instance.maximum x) ≤ a + Instance.maximum y :=
    max_le (le_add_of_nonneg_right hY) hM
  have hR : Instance.maximum y ≤ max a (Instance.maximum x) - a := by
    apply Instance.maximum_le y (sub_nonneg.mpr (le_max_left _ _))
    intro i
    by_cases hx : 0 ≤ x i
    · change excessValueMap a (x i) ≤ _
      rw [excessValueMap_eq_positivePart hx]
      exact max_le (sub_le_sub_right ((Instance.le_maximum x i).trans (le_max_right _ _)) a)
        (sub_nonneg.mpr (le_max_left _ _))
    · have hxn : x i ≤ 0 := (not_le.mp hx).le
      change x i - min a (max (x i) 0) ≤ _
      rw [max_eq_right hxn, min_eq_right ha, sub_zero]
      exact hxn.trans (sub_nonneg.mpr (le_max_left _ _))
  change max a (Instance.maximum x) = a + Instance.maximum y
  linarith only [hL,hR]

noncomputable def Instance.expectedTerminalMaximum (P : Instance n) (a : ℝ) : ℝ :=
  ∫ x, max a (Instance.maximum x) ∂P.valuesLaw

lemma Instance.expectedTerminalMaximum_eq_excess (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a : ℝ} (ha : 0 ≤ a) :
    P.expectedTerminalMaximum a = a + (P.excessOffers a).expectedMaximum := by
  let f : Fin n → ℝ → ℝ := fun _ => excessValueMap a
  have hf : ∀ i, Measurable (f i) := fun _ => measurable_excessValueMap a
  have hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x := fun i => (P.nonnegative i).mono fun _ hx => excessValueMap_nonnegative hx
  have hQ := P.excessOffers_integrable_maximum hP ha
  have hp := P.mapValues_measurePreserving f hf hnn
  have hI : Integrable (fun x : Fin n → ℝ => Instance.maximum (fun i => f i (x i))) P.valuesLaw :=
    hp.integrable_comp_of_integrable hQ
  have he := integral_map (μ := P.valuesLaw) hp.measurable.aemeasurable Instance.measurable_maximum.aestronglyMeasurable
  rw [hp.map_eq] at he
  change (∫ x, max a (Instance.maximum x) ∂P.valuesLaw) = _
  have hpoint : (fun x : Fin n → ℝ => max a (Instance.maximum x)) =
      fun x => a + Instance.maximum (fun i => f i (x i)) := by
    funext x
    exact maximum_with_terminal_eq_excess ha x
  rw [hpoint, integral_add (integrable_const a) hI, integral_const]
  simp only [probReal_univ,one_smul]
  exact congrArg (fun t : ℝ => a + t) he.symm

end ProphetSecretary.Model
