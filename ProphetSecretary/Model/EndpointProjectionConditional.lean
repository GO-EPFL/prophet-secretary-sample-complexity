import ProphetSecretary.Model.SharpNormalizedRegret

/-!
# Boundary projection conditional on explicit endpoint slack

The width is an explicit function only of the cap and supplied endpoint slack.
The finite comparison has regret factor one and assumes explicit positive
lower bounds at both endpoint gaps. Paper correspondence: the endpoint-slack
projection comparison in `lem:scalar-clamp`.
-/

open MeasureTheory Set
namespace ProphetSecretary.Model

noncomputable def endpointProjectionWidth (H d : ℝ) : ℝ := min (1/4) (d/(4*(H+1)))

lemma endpointProjectionWidth_properties {H d : ℝ} (hH : 0≤H) (hd : 0<d) :
    endpointProjectionWidth H d∈Ioo (0:ℝ) (1/2) ∧ 4*(H+1)*endpointProjectionWidth H d≤d := by
  have hL : 0<H+1 := by linarith only [hH]
  have hD : 0<4*(H+1) := mul_pos (by norm_num) hL
  refine ⟨⟨lt_min (by norm_num) (div_pos hd hD),?_⟩,?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  · have h := (le_div_iff₀ hD).mp (min_le_right (1/4:ℝ) (d/(4*(H+1))))
    simpa only [endpointProjectionWidth,mul_comm] using h

private lemma boundary_projection_cost {f : ℝ → ℝ} {L a d : ℝ}
    (hL : 0≤L) (ha0 : 0≤a) (haHalf : a≤1/2) (hWidth : 4*L*a≤d)
    (hLeft : d≤f 0) (hRight : d≤f 1)
    (hNonneg : ∀ x∈Icc (0:ℝ) 1, 0≤f x)
    (hLip : ∀ x∈Icc (0:ℝ) 1, ∀ y∈Icc (0:ℝ) 1, |f x-f y|≤2*L*|x-y|)
    {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    L*|x-max a (min (1-a) x)|≤f x/2 := by
  have hLa := mul_nonneg hL ha0
  have haB : a≤1-a := by linarith only [haHalf]
  by_cases hLow : x<a
  · have hxB : x≤1-a := hLow.le.trans haB
    rw [min_eq_right hxB,max_eq_left hLow.le,abs_of_nonpos (sub_nonpos.mpr hLow.le)]
    have h := (abs_le.mp (hLip x hx 0 (by norm_num))).1
    rw [sub_zero,abs_of_nonneg hx.1] at h
    nlinarith only [h,hLeft,hWidth,hLa]
  · have hax : a≤x := le_of_not_gt hLow
    by_cases hHigh : 1-a<x
    · rw [min_eq_left hHigh.le,max_eq_right haB,abs_of_nonneg (sub_nonneg.mpr hHigh.le)]
      have h := (abs_le.mp (hLip x hx 1 (by norm_num))).1
      rw [abs_of_nonpos (sub_nonpos.mpr hx.2)] at h
      nlinarith only [h,hRight,hWidth,hLa]
    · have hxB : x≤1-a := le_of_not_gt hHigh
      rw [min_eq_right hxB,max_eq_right hax,sub_self,abs_zero,mul_zero]
      linarith only [hNonneg x hx]

variable {n : ℕ}

/-- Conditional finite form of the paper's projection comparison. Both endpoint
slack hypotheses are visible. The supplied width depends only on H and d,
independently of the instance size, law, policy, and training outcome. -/
theorem RandomizedPolicy.scalar_clamp_of_endpoint_slack (π : RandomizedPolicy n) (P : Instance n)
    {H d : ℝ} (hH : 0≤H) (hd : 0<d) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤H)
    (hLeft : d≤normalizedScalarGap P 0) (hRight : d≤normalizedScalarGap P 1)
    {lam r : ℝ} (hlam : lam∈Icc (0:ℝ) 1)
    (hr : π.normalizedRegret P (max (endpointProjectionWidth H d) (min (1-endpointProjectionWidth H d) lam))≤r) :
    normalizedScalarGap P lam/2-r≤π.scalarObjective P lam (1-lam)-
      optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam) := by
  let a := endpointProjectionWidth H d
  have ha := endpointProjectionWidth_properties hH hd
  have hP := P.integrable_maximum_of_bounded hcap
  have hCost : (H+1)*|lam-max a (min (1-a) lam)|≤normalizedScalarGap P lam/2 :=
    boundary_projection_cost (by linarith only [hH]) ha.1.1.le ha.1.2.le ha.2 hLeft hRight
      (fun x hx => normalizedScalarGap_nonnegative P hP hx)
      (fun x hx y hy => normalizedScalarGap_weight_lipschitz_of_bounded P hH hcap hx hy) hlam
  have hRho : max a (min (1-a) lam)∈Icc (0:ℝ) 1 := by
    refine ⟨ha.1.1.le.trans (le_max_left _ _),?_⟩
    have hB : a≤1-a := by linarith only [ha.1.2]
    exact (max_le hB (min_le_left _ _)).trans (by linarith only [ha.1.1])
  have h := π.scalarGap_ge_gap_sub_projectedRegret P hH hcap hlam hRho hr
  linarith only [h,hCost]

end ProphetSecretary.Model
