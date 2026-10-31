import ProphetSecretary.Model.ExcessValueMap
import ProphetSecretary.Model.BellmanResidualBasic
import ProphetSecretary.Model.ZeroSimulationProbability

/-!
# Analytical laws of excess offers

Pushing a probability law through the excess map may create an atom at zero.
These laws are used for finite branch residuals and are not asserted to be
positive Poisson mark intensities. Measurability, first moments and the actual
finite-product law identities are proved explicitly.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

noncomputable def excessLaw (κ : Measure ℝ) (a : ℝ) : Measure ℝ := κ.map (excessValueMap a)

instance excessLaw_probability (κ : Measure ℝ) [IsProbabilityMeasure κ] (a : ℝ) : IsProbabilityMeasure (excessLaw κ a) :=
  Measure.isProbabilityMeasure_map (measurable_excessValueMap a).aemeasurable

lemma excessLaw_nonnegative (κ : Measure ℝ) (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (a : ℝ) :
    ∀ᵐ x ∂excessLaw κ a, 0 ≤ x :=
  (ae_map_iff (measurable_excessValueMap a).aemeasurable measurableSet_Ici).mpr
    (hκ.mono fun _ hx => excessValueMap_nonnegative hx)

lemma integrable_excessValueMap (κ : Measure ℝ) [IsFiniteMeasure κ] (hI : Integrable id κ)
    {a : ℝ} (ha : 0 ≤ a) : Integrable (excessValueMap a) κ := by
  apply (hI.abs.add (integrable_const a)).mono' (measurable_excessValueMap a).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    have hd := excessValueMap_displacement ha x
    calc
      _ = |(excessValueMap a x - x) + x| := by congr 1; ring
      _ ≤ |excessValueMap a x - x| + |x| := abs_add_le _ _
      _ ≤ a + |x| := add_le_add hd le_rfl
      _ = _ := add_comm _ _

lemma excessLaw_integrable (κ : Measure ℝ) [IsFiniteMeasure κ] (hI : Integrable id κ)
    {a : ℝ} (ha : 0 ≤ a) : Integrable id (excessLaw κ a) :=
  (integrable_map_measure aestronglyMeasurable_id (measurable_excessValueMap a).aemeasurable).mpr
    (integrable_excessValueMap κ hI ha)

lemma positivePremium_excessLaw (κ : Measure ℝ) (a w v : ℝ) :
    positivePremium (excessLaw κ a) w v = ∫ x, max (w * excessValueMap a x - v) 0 ∂κ := by
  have hm : Measurable (fun x : ℝ => max (w * x - v) 0) := by fun_prop
  exact integral_map (measurable_excessValueMap a).aemeasurable hm.aestronglyMeasurable

lemma excessLaw_dirac_zero {a : ℝ} (ha : 0 ≤ a) : excessLaw (Measure.dirac 0) a = Measure.dirac 0 := by
  rw [excessLaw,Measure.map_dirac' (measurable_excessValueMap a) 0,excessValueMap_zero ha]

variable {n N : ℕ}

lemma Instance.excessOffers_law (P : Instance n) (a : ℝ) (i : Fin n) :
    (P.excessOffers a).law i = excessLaw (P.law i) a := rfl

lemma Instance.excessOffers_appendZeros (P : Instance n) (N : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (P.appendZeros N).excessOffers a = (P.excessOffers a).appendZeros N := by
  apply Instance.eq_of_law_eq
  funext i
  induction i using Fin.addCases with
  | left i => simp only [Instance.excessOffers,Instance.mapValues,Instance.appendZeros,Fin.addCases_left]
  | right j =>
    change excessLaw ((P.appendZeros N).law (j.natAdd n)) a = _
    simp only [Instance.appendZeros,Fin.addCases_right,excessLaw_dirac_zero ha]

end ProphetSecretary.Model

