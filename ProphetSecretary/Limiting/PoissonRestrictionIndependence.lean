import ProphetSecretary.Limiting.PoissonDisjointFactors
import ProphetSecretary.Limiting.PoissonDisjointCounts
import ProphetSecretary.Probability.RandomMeasureIndependence
import ProphetSecretary.Probability.NaturalVectorIndependence

/-!
# Independent random-measure restrictions of the finite Poisson construction

Disjoint restrictions are independent as complete measurable counting
measures. Test regions inside either restriction may overlap. The proof uses
the actual generating functional and finite-evaluation independence criterion.
-/

open MeasureTheory ProbabilityTheory Set Filter Complex
open scoped Classical BigOperators ENNReal

namespace ProphetSecretary.Limiting

lemma measurable_countingMeasure_restrict {U : Set Point} (hU : MeasurableSet U) :
    Measurable (fun ω => (countingMeasure ω).restrict U) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have he : (fun ω => ((countingMeasure ω).restrict U) S) = fun ω => countingMeasure ω (S ∩ U) := by
    funext ω
    exact Measure.restrict_apply hS
  rw [he]
  exact (Measure.measurable_coe (hS.inter hU)).comp measurable_countingMeasure

theorem countingMeasure_restrictions_independent (μ : FiniteMeasure ℝ)
    {U V : Set Point} (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : Disjoint U V) :
    IndepFun (fun ω => (countingMeasure ω).restrict U) (fun ω => (countingMeasure ω).restrict V)
      (configurationLaw μ) := by
  have hFinite (W : Set Point) : ∀ᵐ ω ∂configurationLaw μ, ((countingMeasure ω).restrict W) univ < ⊤ :=
    Filter.Eventually.of_forall (fun ω => by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono (subset_univ W)).trans_lt (by rw [countingMeasure_univ]; exact ENNReal.natCast_lt_top _))
  apply ProphetSecretary.Probability.indepFun_finiteRandomMeasures_of_finite_real_evaluations
    (measurable_countingMeasure_restrict hU) (measurable_countingMeasure_restrict hV) (hFinite U) (hFinite V)
  intro I J
  let S := fun i : I => i.1.1 ∩ U
  let T := fun j : J => j.1.1 ∩ V
  have hS (i : I) : MeasurableSet (S i) := i.1.2.inter hU
  have hT (j : J) : MeasurableSet (T j) := j.1.2.inter hV
  have hXN : Measurable (fun ω => fun i : I => pointCount (S i) ω) :=
    measurable_pi_lambda _ (fun i => measurable_pointCount (hS i))
  have hYN : Measurable (fun ω => fun j : J => pointCount (T j) ω) :=
    measurable_pi_lambda _ (fun j => measurable_pointCount (hT j))
  have hInd := ProphetSecretary.Probability.indepFun_natCastVectors_of_generating_factorization
    (P := configurationLaw μ) hXN hYN (fun z w hz hw => by
      let g := fun p => ∏ i : I, pointFactor (S i) (z i) p
      let h := fun p => ∏ j : J, pointFactor (T j) (w j) p
      have hg : Measurable g := Finset.measurable_fun_prod _ (fun i _ => measurable_pointFactor (hS i) (z i))
      have hh : Measurable h := Finset.measurable_fun_prod _ (fun j _ => measurable_pointFactor (hT j) (w j))
      have hgN (p : Point) : ‖g p‖ ≤ 1 := by
        dsimp only [g]
        rw [norm_prod]
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => pointFactor_norm_le_one (S i) (hz i) p)
      have hhN (p : Point) : ‖h p‖ ≤ 1 := by
        dsimp only [h]
        rw [norm_prod]
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => pointFactor_norm_le_one (T j) (hw j) p)
      have hgOut (p : Point) (hp : p ∉ U) : g p = 1 := by
        apply Finset.prod_eq_one
        intro i _
        exact if_neg (fun hi : p ∈ S i => hp hi.2)
      have hhOut (p : Point) (hp : p ∉ V) : h p = 1 := by
        apply Finset.prod_eq_one
        intro j _
        exact if_neg (fun hj : p ∈ T j => hp hj.2)
      have hpg (ω : Configuration) : pointProd g ω = ∏ i : I, z i ^ pointCount (S i) ω :=
        pointProd_prod_pointFactor S z ω
      have hph (ω : Configuration) : pointProd h ω = ∏ j : J, w j ^ pointCount (T j) ω :=
        pointProd_prod_pointFactor T w ω
      simpa only [hpg,hph] using integral_pointProd_mul_of_disjoint_support μ hUV g h hg hh hgN hhN hgOut hhOut)
  have hXeq : (fun ω => fun i : I => ((countingMeasure ω).restrict U).real i.1.1) =
      (fun ω => fun i : I => (pointCount (S i) ω : ℝ)) := by
    funext ω i
    change (((countingMeasure ω).restrict U) i.1.1).toReal = _
    rw [Measure.restrict_apply i.1.2,countingMeasure_eq_pointCount (hS i),ENNReal.toReal_natCast]
  have hYeq : (fun ω => fun j : J => ((countingMeasure ω).restrict V).real j.1.1) =
      (fun ω => fun j : J => (pointCount (T j) ω : ℝ)) := by
    funext ω j
    change (((countingMeasure ω).restrict V) j.1.1).toReal = _
    rw [Measure.restrict_apply j.1.2,countingMeasure_eq_pointCount (hT j),ENNReal.toReal_natCast]
  rw [hXeq,hYeq]
  exact hInd

end ProphetSecretary.Limiting
