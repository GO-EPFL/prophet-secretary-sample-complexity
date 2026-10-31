import ProphetSecretary.Model.BoundaryNormalization
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A normalized countersequence to uniform reward-boundary slack

Failure of uniform positive slack supplies finite counterexamples with gaps
less than mu/(m+1). Normalization is performed before any compact extraction:
every new expected maximum is one, the common cap is H/mu, and reward-only
optimal values converge to the global constant C_PS.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model

lemma exists_normalized_boundary_countersequence (H : ℝ≥0) (mu : ℝ) (hmu : 0<mu)
    (hFail : ∀ d : ℝ, 0<d → ∃ (n : ℕ) (P : Instance n),
      (∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ)) ∧ mu≤P.expectedMaximum ∧
      optimalScalarValue P 1 0-optimalCompetitiveRatio*P.expectedMaximum<d) :
    ∃ (sizes : ℕ → ℕ) (Q : ∀ m, Instance (sizes m)),
      (∀ m i, ∀ᵐ x ∂(Q m).law i, x≤(boundaryNormalizedCap H mu hmu:ℝ)) ∧
      (∀ m, (Q m).expectedMaximum=1) ∧
      Tendsto (fun m => optimalScalarValue (Q m) 1 0) atTop (𝓝 optimalCompetitiveRatio) := by
  have hWitness (m : ℕ) : ∃ (n : ℕ) (P : Instance n),
      (∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ)) ∧ mu≤P.expectedMaximum ∧
      optimalScalarValue P 1 0-optimalCompetitiveRatio*P.expectedMaximum<mu/((m:ℝ)+1) :=
    hFail _ (div_pos hmu (by positivity))
  choose sizes P hCap hMean hGap using hWitness
  let Q : ∀ m, Instance (sizes m) := fun m => (P m).normalizeMaximum (hmu.trans_le (hMean m))
  have hQCap (m : ℕ) (i : Fin (sizes m)) :
      ∀ᵐ x ∂(Q m).law i, x≤(boundaryNormalizedCap H mu hmu:ℝ) :=
    (P m).normalizeMaximum_bounded hmu (hCap m) (hMean m) i
  have hQM (m : ℕ) : (Q m).expectedMaximum=1 := (P m).normalizeMaximum_expectedMaximum _
  have hPI (m : ℕ) : Integrable Instance.maximum (P m).valuesLaw := (P m).integrable_maximum_of_bounded (hCap m)
  have hQI (m : ℕ) : Integrable Instance.maximum (Q m).valuesLaw := (Q m).integrable_maximum_of_bounded (hQCap m)
  have hLow (m : ℕ) : optimalCompetitiveRatio≤optimalScalarValue (Q m) 1 0 := by
    have h := globalScalar_inequality_of_integrable (Q m) (hQI m) zero_le_one le_rfl
    simpa only [hQM,one_mul,add_zero,mul_one] using h
  have hHigh (m : ℕ) : optimalScalarValue (Q m) 1 0-optimalCompetitiveRatio≤1/((m:ℝ)+1) := by
    have hM : 0<(P m).expectedMaximum := hmu.trans_le (hMean m)
    have hEq := (P m).normalizeMaximum_rewardGap (hPI m) hM
    change optimalScalarValue (Q m) 1 0-optimalCompetitiveRatio=_ at hEq
    rw [hEq]
    apply (div_le_iff₀ hM).mpr
    have hScale := div_le_div_of_nonneg_right (hMean m) (show (0:ℝ)≤(m:ℝ)+1 by positivity)
    calc
      _ ≤ mu/((m:ℝ)+1) := (hGap m).le
      _ ≤ (P m).expectedMaximum/((m:ℝ)+1) := hScale
      _ = _ := by ring
  have hLimit : Tendsto (fun m => optimalScalarValue (Q m) 1 0-optimalCompetitiveRatio) atTop (𝓝 0) :=
    squeeze_zero (fun m => sub_nonneg.mpr (hLow m)) hHigh (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  refine ⟨sizes,Q,hQCap,hQM,?_⟩
  simpa only [sub_add_cancel,zero_add] using hLimit.add_const optimalCompetitiveRatio

end ProphetSecretary.Limiting
