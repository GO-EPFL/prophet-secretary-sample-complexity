import ProphetSecretary.Limiting.WeakHybridBenchmark
import ProphetSecretary.Limiting.ExcessIntensityOrder

/-!
# An explicit CDF error for ordered finite Poisson intensities

The retained product factor is bounded by one. The Poisson void difference is
at most the total added intensity, uniformly in the retained dimension.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma hybrid_maximum_cdf_intensity_order (P : Model.Instance n) (μ ν : FiniteMeasure ℝ)
    (hOrder : (μ : Measure ℝ) ≤ (ν : Measure ℝ)) (a : ℝ≥0) {t : ℝ} (hat : (a : ℝ) ≤ t) :
    0 ≤ (hybridValueLaw P μ).real {v | hybridMaximum a v ≤ t}-
      (hybridValueLaw P ν).real {v | hybridMaximum a v ≤ t} ∧
    (hybridValueLaw P μ).real {v | hybridMaximum a v ≤ t}-
      (hybridValueLaw P ν).real {v | hybridMaximum a v ≤ t} ≤
        (finiteIntensityDifference ν μ : Measure ℝ).real univ := by
  let ρ := finiteIntensityDifference ν μ
  have hAdd := add_finiteIntensityDifference ν μ hOrder
  have he := congrArg (fun κ : FiniteMeasure ℝ => (κ : Measure ℝ).real (Ioi t)) hAdd
  change ((μ : Measure ℝ)+(ρ : Measure ℝ)).real (Ioi t) = (ν : Measure ℝ).real (Ioi t) at he
  rw [measureReal_add_apply] at he
  have hν : (ν : Measure ℝ).real (Ioi t) = (μ : Measure ℝ).real (Ioi t)+(ρ : Measure ℝ).real (Ioi t) := he.symm
  have hd : 0 ≤ (ρ : Measure ℝ).real (Ioi t) := measureReal_nonneg
  have hVoid0 : 0 ≤ 1-Real.exp (-(ρ : Measure ℝ).real (Ioi t)) := by
    have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hd)
    linarith only [h]
  have hVoid1 : 1-Real.exp (-(ρ : Measure ℝ).real (Ioi t)) ≤ (ρ : Measure ℝ).real (Ioi t) := by
    have h := Real.add_one_le_exp (-(ρ : Measure ℝ).real (Ioi t))
    linarith only [h]
  let F := Real.exp (-(μ : Measure ℝ).real (Ioi t))*(∏ i, (P.law i).real (Iic t))
  have hF0 : 0 ≤ F := mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun _ _ => measureReal_nonneg))
  have hF1 : F ≤ 1 := by
    have hExp := Real.exp_le_one_iff.mpr (show -(μ : Measure ℝ).real (Ioi t) ≤ 0 from neg_nonpos.mpr measureReal_nonneg)
    have hProd : (∏ i, (P.law i).real (Iic t)) ≤ 1 :=
      Finset.prod_le_one (fun _ _ => measureReal_nonneg) (fun _ _ => measureReal_le_one)
    exact (mul_le_mul hExp hProd (Finset.prod_nonneg (fun _ _ => measureReal_nonneg)) zero_le_one).trans_eq (mul_one 1)
  have hUpper := mul_le_mul_of_nonneg_left hVoid1 hF0
  have hLower := mul_nonneg hF0 hVoid0
  have hMass : (ρ : Measure ℝ).real (Ioi t) ≤ (ρ : Measure ℝ).real univ := measureReal_mono (subset_univ _)
  have hPoint : (hybridValueLaw P μ).real {v | hybridMaximum a v ≤ t}-
      (hybridValueLaw P ν).real {v | hybridMaximum a v ≤ t} =
      F*(1-Real.exp (-(ρ : Measure ℝ).real (Ioi t))) := by
    rw [hybridMaximum_real_Iic P μ (a.property.trans hat) hat,
      hybridMaximum_real_Iic P ν (a.property.trans hat) hat,hν,neg_add,Real.exp_add]
    dsimp only [F]
    ring
  rw [hPoint]
  exact ⟨hLower,by nlinarith only [hUpper,hF1,hMass,hd]⟩

end ProphetSecretary.Limiting
