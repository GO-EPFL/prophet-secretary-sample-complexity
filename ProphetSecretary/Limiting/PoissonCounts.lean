import ProphetSecretary.Limiting.GeneratingFunctional

/-!
# Poisson laws of finite band counts

Thinning is derived from the generating functional and the library's characteristic
function uniqueness theorem. Counts refer to actual points, including points after an
online policy stops, and remain analytical variables.
-/

open MeasureTheory ProbabilityTheory Set Complex
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

noncomputable def pointCount (S : Set Point) (ω : Configuration) : ℕ :=
  ∑ j : Fin ω.1, if ω.2 j ∈ S then 1 else 0

lemma measurable_pointCount {S : Set Point} (hS : MeasurableSet S) : Measurable (pointCount S) := by
  apply measurable_of_configuration_branches
  intro N
  change Measurable (fun v : Fin N → Point => ∑ j : Fin N, if v j ∈ S then (1 : ℕ) else 0)
  exact Finset.measurable_fun_sum _ (fun j _ => Measurable.ite (hS.preimage (measurable_pi_apply j))
    measurable_const measurable_const)

lemma countingMeasure_eq_pointCount {S : Set Point} (hS : MeasurableSet S) (ω : Configuration) :
    countingMeasure ω S = (pointCount S ω : ℝ≥0∞) := by
  simp only [countingMeasure, pointCount, Measure.coe_finsetSum, Finset.sum_apply, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.dirac_apply' _ hS]
  by_cases hj : ω.2 j ∈ S <;> simp [Set.indicator, hj]

noncomputable def pointFactor (S : Set Point) (z : ℂ) (p : Point) : ℂ := if p ∈ S then z else 1

lemma measurable_pointFactor {S : Set Point} (hS : MeasurableSet S) (z : ℂ) :
    Measurable (pointFactor S z) := Measurable.ite hS measurable_const measurable_const

lemma pointFactor_norm_le_one (S : Set Point) {z : ℂ} (hz : ‖z‖ ≤ 1) (p : Point) :
    ‖pointFactor S z p‖ ≤ 1 := by
  unfold pointFactor
  split_ifs
  · exact hz
  · simp

lemma pointProd_pointFactor (S : Set Point) (z : ℂ) (ω : Configuration) :
    pointProd (pointFactor S z) ω = z ^ pointCount S ω := by
  unfold pointProd pointCount pointFactor
  calc
    _ = ∏ j : Fin ω.1, z ^ (if ω.2 j ∈ S then (1 : ℕ) else 0) := by
      apply Finset.prod_congr rfl
      intro j _
      split_ifs <;> simp
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

lemma integral_pointFactor (μ : FiniteMeasure ℝ) {S : Set Point} (hS : MeasurableSet S) (z : ℂ) :
    (∫ p, pointFactor S z p ∂pointLaw μ) = 1 + ((pointLaw μ).real S : ℂ) * (z - 1) := by
  have he : pointFactor S z = fun p => 1 + S.indicator (fun _ => z - 1) p := by
    funext p
    by_cases hp : p ∈ S <;> simp [pointFactor, hp]
  rw [he, integral_add (integrable_const (1 : ℂ)) ((integrable_const (z - 1)).indicator hS),
    integral_const, integral_indicator hS, integral_const]
  simp [measureReal_def]

noncomputable def countRate (μ : FiniteMeasure ℝ) (S : Set Point) : ℝ≥0 := (intensity μ S).toNNReal

lemma countRate_coe (μ : FiniteMeasure ℝ) (S : Set Point) :
    (countRate μ S : ℝ) = (μ.mass : ℝ) * (pointLaw μ).real S := by
  change (intensity μ S).toReal = _
  rw [intensity_eq_mass_smul_pointLaw, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rfl

lemma countRate_coe_eq_intensity (μ : FiniteMeasure ℝ) (S : Set Point) :
    (countRate μ S : ℝ) = (intensity μ).real S := rfl

lemma charFun_pointCount (μ : FiniteMeasure ℝ) {S : Set Point} (hS : MeasurableSet S) (t : ℝ) :
    charFun ((configurationLaw μ).map (fun ω => (pointCount S ω : ℝ))) t =
      Complex.exp (((countRate μ S : ℝ) : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
  have hm : Measurable (fun ω => (pointCount S ω : ℝ)) := ((Measurable.of_discrete : Measurable (fun N : ℕ => (N : ℝ))).comp (measurable_pointCount hS))
  rw [charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  simp only [Real.inner_apply]
  have he (ω : Configuration) : Complex.exp (((pointCount S ω : ℝ) * t : ℝ) * Complex.I) =
      pointProd (pointFactor S (Complex.exp ((t : ℂ) * Complex.I))) ω := by
    rw [pointProd_pointFactor, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [he]
  have hnorm : ‖Complex.exp ((t : ℂ) * Complex.I)‖ ≤ 1 := by simp [Complex.norm_exp]
  rw [generating_functional μ _ (measurable_pointFactor hS _)
    (pointFactor_norm_le_one S hnorm), integral_pointFactor μ hS]
  congr 1
  rw [countRate_coe]
  push_cast
  ring

lemma pointCount_real_law (μ : FiniteMeasure ℝ) {S : Set Point} (hS : MeasurableSet S) :
    (configurationLaw μ).map (fun ω => (pointCount S ω : ℝ)) =
      (poissonMeasure (countRate μ S)).map (Nat.cast : ℕ → ℝ) := by
  haveI : IsProbabilityMeasure ((configurationLaw μ).map (fun ω => (pointCount S ω : ℝ))) :=
    Measure.isProbabilityMeasure_map (((Measurable.of_discrete : Measurable (fun N : ℕ => (N : ℝ))).comp (measurable_pointCount hS)).aemeasurable)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_pointCount μ hS, charFun_map_cast_poissonMeasure]

/-- Exact Poisson thinning law for every measurable time/mark band. -/
lemma pointCount_law (μ : FiniteMeasure ℝ) {S : Set Point} (hS : MeasurableSet S) :
    (configurationLaw μ).map (pointCount S) = poissonMeasure (countRate μ S) := by
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  rw [Measure.map_map (by fun_prop) (measurable_pointCount hS)]
  exact pointCount_real_law μ hS

lemma pointCount_measurePreserving (μ : FiniteMeasure ℝ) {S : Set Point} (hS : MeasurableSet S) :
    MeasurePreserving (pointCount S) (configurationLaw μ) (poissonMeasure (countRate μ S)) :=
  ⟨measurable_pointCount hS, pointCount_law μ hS⟩

lemma pointCount_integrable (μ : FiniteMeasure ℝ) {S : Set Point} (hS : MeasurableSet S) :
    Integrable (fun ω => (pointCount S ω : ℝ)) (configurationLaw μ) :=
  (pointCount_measurePreserving μ hS).integrable_comp_of_integrable (poisson_first_integrable (countRate μ S))

lemma integral_pointCount (μ : FiniteMeasure ℝ) {S : Set Point} (hS : MeasurableSet S) :
    (∫ ω, (pointCount S ω : ℝ) ∂configurationLaw μ) = (intensity μ).real S := by
  have he := integral_map (μ := configurationLaw μ) (measurable_pointCount hS).aemeasurable
    (Measurable.of_discrete : Measurable (fun N : ℕ => (N : ℝ))).aestronglyMeasurable
  rw [pointCount_law μ hS, integral_poisson_first] at he
  exact he.symm

lemma pointCount_second_integrable (μ : FiniteMeasure ℝ) {S : Set Point} (hS : MeasurableSet S) :
    Integrable (fun ω => (pointCount S ω : ℝ) ^ 2) (configurationLaw μ) :=
  (pointCount_measurePreserving μ hS).integrable_comp_of_integrable
    (g := fun N : ℕ => (N : ℝ) ^ 2) (poisson_second_integrable (countRate μ S))

lemma integral_pointCount_second (μ : FiniteMeasure ℝ) {S : Set Point} (hS : MeasurableSet S) :
    (∫ ω, (pointCount S ω : ℝ) ^ 2 ∂configurationLaw μ) = ((intensity μ).real S) ^ 2 + (intensity μ).real S := by
  have he := integral_map (μ := configurationLaw μ) (measurable_pointCount hS).aemeasurable
    (Measurable.of_discrete : Measurable (fun N : ℕ => (N : ℝ) ^ 2)).aestronglyMeasurable
  rw [pointCount_law μ hS, integral_poisson_second] at he
  exact he.symm

end ProphetSecretary.Limiting
