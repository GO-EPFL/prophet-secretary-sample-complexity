import ProphetSecretary.Model.ScalarValueProperties

/-!
# Joint measurability of fixed-law scalar coefficients

The coefficient Lipschitz estimate over the complete admissible policy class gives a
continuous total extension from the nonnegative quadrant, including reward weight zero.
-/

open MeasureTheory Set
open scoped NNReal

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- Joint true-law value measurability is obtained from the actual coefficient
Lipschitz estimate. Clamping supplies a total measurable extension of the nonnegative quadrant. -/
lemma Instance.continuous_clampedScalarValue (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    Continuous (fun z : ℝ × ℝ => optimalScalarValue P (max 0 z.1) (max 0 z.2)) := by
  let K : ℝ≥0 := ⟨P.expectedMaximum + 1, by linarith [P.expectedMaximum_nonnegative]⟩
  have hLip : LipschitzOnWith K (fun z : ℝ × ℝ => optimalScalarValue P z.1 z.2)
      (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z hz z' hz'
    rw [Real.dist_eq]
    have hfst : |z.1 - z'.1| ≤ dist z z' := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_left _ _
    have hsnd : |z.2 - z'.2| ≤ dist z z' := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_right _ _
    calc
      _ ≤ P.expectedMaximum * |z.1 - z'.1| + |z.2 - z'.2| :=
        optimalScalarValue_coefficients_lipschitz P hP hz.1 hz.2 hz'.1 hz'.2
      _ ≤ P.expectedMaximum * dist z z' + dist z z' :=
        add_le_add (mul_le_mul_of_nonneg_left hfst P.expectedMaximum_nonnegative) hsnd
      _ = (K : ℝ) * dist z z' := by
        change P.expectedMaximum * dist z z' + dist z z' = (P.expectedMaximum + 1) * dist z z'
        ring
  exact hLip.continuousOn.comp_continuous
    ((continuous_const.max continuous_fst).prodMk (continuous_const.max continuous_snd))
    (fun z => ⟨le_max_left (0 : ℝ) z.1, le_max_left (0 : ℝ) z.2⟩)

lemma Instance.measurable_scalarValue_coefficients (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {Ω : Type*} [MeasurableSpace Ω]
    {W C : Ω → ℝ} (hW : Measurable W) (hC : Measurable C)
    (hW0 : ∀ ω, 0 ≤ W ω) (hC0 : ∀ ω, 0 ≤ C ω) :
    Measurable fun ω => optimalScalarValue P (W ω) (C ω) := by
  have hm := (P.continuous_clampedScalarValue hP).measurable.comp (hW.prodMk hC)
  convert hm using 1
  funext ω
  simp only [Function.comp_def, max_eq_right (hW0 ω), max_eq_right (hC0 ω)]

end ProphetSecretary.Model
