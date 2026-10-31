import ProphetSecretary.Model.EndpointProjectionConditional

/-!
# Scalar-gap slack outside the endpoint projection interval

The explicit interval width depends only on a common cap and endpoint
slack. Lipschitz continuity transfers half of that slack to both boundary
intervals. The endpoint hypotheses are displayed and are not assumed to
hold for every instance without the boundary-slack theorem.
-/

open MeasureTheory Set
namespace ProphetSecretary.Model

lemma Instance.normalizedScalarGap_outside_projection_lower_bound {n : ℕ} (P : Instance n)
    {H d : ℝ} (hH : 0≤H) (hd : 0<d) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤H)
    (hLeft : d≤normalizedScalarGap P 0) (hRight : d≤normalizedScalarGap P 1)
    {lam : ℝ} (hlam : lam∈Icc (0 : ℝ) 1)
    (hBoundary : lam<endpointProjectionWidth H d ∨ 1-endpointProjectionWidth H d<lam) :
    d/2≤normalizedScalarGap P lam := by
  have hWidth := (endpointProjectionWidth_properties hH hd).2
  have hL : 0≤H+1 := by linarith only [hH]
  rcases hBoundary with hLow|hHigh
  · have hLip := (abs_le.mp (normalizedScalarGap_weight_lipschitz_of_bounded P hH hcap
      hlam (by norm_num : (0 : ℝ)∈Icc 0 1))).1
    rw [sub_zero,abs_of_nonneg hlam.1] at hLip
    have hCost := mul_le_mul_of_nonneg_left hLow.le hL
    nlinarith only [hLip,hLeft,hWidth,hCost]
  · have hLip := (abs_le.mp (normalizedScalarGap_weight_lipschitz_of_bounded P hH hcap
      hlam (by norm_num : (1 : ℝ)∈Icc 0 1))).1
    rw [abs_of_nonpos (sub_nonpos.mpr hlam.2)] at hLip
    have hDist : 1-lam≤endpointProjectionWidth H d := by linarith only [hHigh]
    have hCost := mul_le_mul_of_nonneg_left hDist hL
    nlinarith only [hLip,hRight,hWidth,hCost]

end ProphetSecretary.Model
