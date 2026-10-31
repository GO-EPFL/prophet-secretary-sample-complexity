import ProphetSecretary.Limiting.RareDesignBenchmark
import ProphetSecretary.Limiting.PoissonizedFamily
import ProphetSecretary.Limiting.IndependentAppend
import ProphetSecretary.Analysis.BernoulliVoidComparison

/-!
# Benchmark CDF error for independent rare offers and Poisson intensity

This is a comparison of the actual maximum laws, independent of online value.
The Bernoulli void inequality retains the sum of squared rare probabilities.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {n m : ℕ}

lemma positiveOfferIntensity_real_Ioi (R : Model.Instance m) {t : ℝ} (ht : 0 ≤ t) :
    (positiveOfferIntensity R : Measure ℝ).real (Ioi t) = ∑ i, (R.law i).real (Ioi t) := by
  unfold Measure.real
  rw [positiveOfferIntensity_toMeasure,Measure.finsetSum_apply,
    ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.restrict_apply measurableSet_Ioi,inter_eq_left.mpr (Ioi_subset_Ioi ht)]

lemma finite_poisson_maximum_cdf_comparison (P : Model.Instance n) (R : Model.Instance m)
    (H : ℝ≥0) (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hR : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    let B := poissonizedFamily P R H hP hR
    0 ≤ (hybridValueLaw P B.intensity).real {v | hybridMaximum 0 v ≤ t}-
      (P.appendIndependent R).valuesLaw.real {x | Model.Instance.maximum x ≤ t} ∧
    (hybridValueLaw P B.intensity).real {v | hybridMaximum 0 v ≤ t}-
      (P.appendIndependent R).valuesLaw.real {x | Model.Instance.maximum x ≤ t} ≤
      ∑ i, ((R.law i).real (Ioi t))^2 := by
  let p : Fin m → ℝ := fun i => (R.law i).real (Ioi t)
  have hVoid := ProphetSecretary.Analysis.bernoulli_void_comparison p
    (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
  have hCDF (i : Fin m) : (R.law i).real (Iic t) = 1-p i := by
    rw [show Iic t = (Ioi t)ᶜ by ext x; simp,measureReal_compl measurableSet_Ioi,probReal_univ]
  have hFac0 : 0 ≤ ∏ i : Fin n, (P.law i).real (Iic t) := Finset.prod_nonneg (fun _ _ => measureReal_nonneg)
  have hFac1 : (∏ i : Fin n, (P.law i).real (Iic t)) ≤ 1 := by
    exact Finset.prod_le_one (fun _ _ => measureReal_nonneg) (fun _ _ => measureReal_le_one)
  dsimp only
  rw [hybridMaximum_real_Iic P _ ht ht,finite_maximum_real_Iic _ ht,Fin.prod_univ_add]
  simp only [Model.Instance.appendIndependent,Fin.addCases_left,Fin.addCases_right]
  simp only [poissonizedFamily,positiveOfferIntensity_real_Ioi R ht,hCDF]
  constructor
  · nlinarith only [hVoid.1,hFac0]
  · have hUpper := mul_le_mul_of_nonneg_left hVoid.2 hFac0
    have hSq : 0 ≤ ∑ i : Fin m, p i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith only [hUpper,hFac1,hSq]

end ProphetSecretary.Limiting
