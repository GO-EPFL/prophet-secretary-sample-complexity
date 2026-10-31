import ProphetSecretary.Model.ScalarClamp

/-!
# Uniform interior localization of small critical sublevels

The two endpoint gaps and the common gap Lipschitz constant yield a uniform
positive gap outside a fixed interior interval. Thus every sufficiently small
critical sublevel lies inside that interval. This is the unnamed localization
claim between `lem:boundary-slack` and `lem:scalar-clamp`.
-/

open MeasureTheory Set
open scoped NNReal Classical
namespace ProphetSecretary.Model

theorem bounded_boundary_sublevel_localization (H : ℝ≥0) (mu : ℝ) (hmu : 0<mu) :
    ∃ a d0 : ℝ, a∈Ioo (0:ℝ) (1/2) ∧ 0<d0 ∧ ∀ (n : ℕ) (P : Instance n),
      (∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ)) → mu≤P.expectedMaximum →
      (∀ lam : ℝ, lam∈Icc (0:ℝ) 1 → lam∉Icc a (1-a) → d0≤normalizedScalarGap P lam) ∧
      (∀ lam : ℝ, lam∈Icc (0:ℝ) 1 → normalizedScalarGap P lam<d0 → lam∈Icc a (1-a)) := by
  obtain ⟨d,hd,hSlack⟩ := bounded_reward_boundary_slack H mu hmu
  let D := min d (1-optimalCompetitiveRatio)
  have hD : 0<D := lt_min hd (by linarith only [optimalCompetitiveRatio_le_threeQuarters])
  let a := endpointProjectionWidth (H:ℝ) D
  have ha := endpointProjectionWidth_properties H.property hD
  have hL : 0≤2*((H:ℝ)+1) := by positivity
  have hWidth : 4*((H:ℝ)+1)*a≤D := ha.2
  have hMaxCost : 2*((H:ℝ)+1)*a≤D/2 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    calc
      _ = 4*((H:ℝ)+1)*a := by ring
      _ ≤ D := hWidth
  refine ⟨a,D/2,ha.1,div_pos hD (by norm_num),?_⟩
  intro n P hcap hMean
  have hLeft : D≤normalizedScalarGap P 0 := by rw [normalizedScalarGap_zero];exact min_le_right _ _
  have hRight : D≤normalizedScalarGap P 1 := by
    rw [normalizedScalarGap_one]
    exact (min_le_left _ _).trans (hSlack n P hcap hMean)
  have hOutside (lam : ℝ) (hlam : lam∈Icc (0:ℝ) 1) (hNot : lam∉Icc a (1-a)) : D/2≤normalizedScalarGap P lam := by
    have hCases : lam<a ∨ 1-a<lam := by simpa only [Set.mem_Icc,not_and_or,not_le] using hNot
    rcases hCases with hLow | hHigh
    · have hLip := normalizedScalarGap_weight_lipschitz_of_bounded P H.property hcap hlam (show (0:ℝ)∈Icc 0 1 by norm_num)
      have hAbs : |normalizedScalarGap P 0-normalizedScalarGap P lam|≤2*((H:ℝ)+1)*|lam-0| := by
        rw [abs_sub_comm]
        exact hLip
      have h : normalizedScalarGap P 0-normalizedScalarGap P lam≤2*((H:ℝ)+1)*|lam-0| :=
        (le_abs_self _).trans hAbs
      rw [sub_zero,abs_of_nonneg hlam.1] at h
      have hCost := mul_le_mul_of_nonneg_left hLow.le hL
      linarith only [h,hLeft,hCost,hMaxCost]
    · have hLip := normalizedScalarGap_weight_lipschitz_of_bounded P H.property hcap hlam (show (1:ℝ)∈Icc 0 1 by norm_num)
      have hAbs : |normalizedScalarGap P 1-normalizedScalarGap P lam|≤2*((H:ℝ)+1)*|lam-1| := by
        rw [abs_sub_comm]
        exact hLip
      have h : normalizedScalarGap P 1-normalizedScalarGap P lam≤2*((H:ℝ)+1)*|lam-1| :=
        (le_abs_self _).trans hAbs
      rw [abs_of_nonpos (sub_nonpos.mpr hlam.2)] at h
      have hNeg : -(lam-1)=1-lam := by ring
      rw [hNeg] at h
      have hCost := mul_le_mul_of_nonneg_left (show 1-lam≤a by linarith only [hHigh]) hL
      linarith only [h,hRight,hCost,hMaxCost]
  refine ⟨hOutside,?_⟩
  intro lam hlam hSmall
  by_contra hNot
  exact (not_lt_of_ge (hOutside lam hlam hNot)) hSmall

end ProphetSecretary.Model
