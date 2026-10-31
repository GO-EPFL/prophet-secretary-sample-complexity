import ProphetSecretary.Limiting.GeneratingFunctionalIntensity

/-!
# Factorization of Poisson tests on disjoint regions

The functions equal one outside disjoint regions. Additivity of the actual
intensity exponent then proves factorization of their configuration tests.
-/

open MeasureTheory Set Filter Complex
open scoped Classical BigOperators

namespace ProphetSecretary.Limiting

lemma pointProd_mul (g h : Point → ℂ) (ω : Configuration) :
    pointProd (fun p => g p*h p) ω = pointProd g ω * pointProd h ω := by
  unfold pointProd
  exact Finset.prod_mul_distrib

theorem integral_pointProd_mul_of_disjoint_support (μ : FiniteMeasure ℝ)
    {U V : Set Point} (hUV : Disjoint U V) (g h : Point → ℂ)
    (hg : Measurable g) (hh : Measurable h)
    (hgN : ∀ p, ‖g p‖ ≤ 1) (hhN : ∀ p, ‖h p‖ ≤ 1)
    (hgOut : ∀ p, p ∉ U → g p = 1) (hhOut : ∀ p, p ∉ V → h p = 1) :
    (∫ ω, pointProd g ω * pointProd h ω ∂configurationLaw μ) =
      (∫ ω, pointProd g ω ∂configurationLaw μ) * (∫ ω, pointProd h ω ∂configurationLaw μ) := by
  have hprodN (p : Point) : ‖g p*h p‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hgN p) (hhN p) (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hgI : Integrable (fun p => g p-1) (intensity μ) :=
    (Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall hgN)).sub (integrable_const 1)
  have hhI : Integrable (fun p => h p-1) (intensity μ) :=
    (Integrable.of_bound hh.aestronglyMeasurable 1 (Filter.Eventually.of_forall hhN)).sub (integrable_const 1)
  have hprod : (fun ω => pointProd g ω * pointProd h ω) = pointProd (fun p => g p*h p) :=
    funext (fun ω => (pointProd_mul g h ω).symm)
  have hsum : (fun p => g p*h p-1) = (fun p => (g p-1)+(h p-1)) := by
    funext p
    by_cases hp : p ∈ U
    · have hpV : p ∉ V := fun hv => Set.disjoint_left.mp hUV hp hv
      rw [hhOut p hpV]
      ring
    · rw [hgOut p hp]
      ring
  have hm : Measurable (fun p => g p*h p) := hg.mul hh
  rw [hprod,generating_functional_intensity μ (fun p => g p*h p) hm hprodN,
    generating_functional_intensity μ g hg hgN,generating_functional_intensity μ h hh hhN,
    hsum,integral_add hgI hhI,Complex.exp_add]

end ProphetSecretary.Limiting
