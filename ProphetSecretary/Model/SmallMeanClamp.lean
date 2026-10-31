import ProphetSecretary.Model.ScalarClamp
import ProphetSecretary.Model.SmallMeanLowerClamp

/-!
# The small-mean scalar clamp

Paper correspondence: `cor:small-mean-clamp`. The lower endpoint is exactly
4/5. Uniform reward-boundary slack supplies the upper endpoint b>4/5. The
lower-target duration estimate and the upper boundary comparison give regret
multiplier K=5. The queried duration/reward ratios lie in the stated interval.
-/

open MeasureTheory Set
open scoped NNReal Classical
namespace ProphetSecretary.Model

private lemma upper_boundary_cost {f : ℝ → ℝ} {a d x : ℝ}
    (hWidth : 8*a≤d) (hRight : d≤f 1) (hxLow : 1-a≤x) (hxHigh : x≤1)
    (hLip : |f x-f 1|≤4*|x-1|) : 2*|x-(1-a)|≤f x/2 := by
  have h := (abs_le.mp hLip).1
  rw [abs_of_nonpos (sub_nonpos.mpr hxHigh)] at h
  rw [abs_of_nonneg (sub_nonneg.mpr hxLow)]
  nlinarith only [h,hRight,hWidth,hxLow,hxHigh]

private lemma upper_boundary_slack {f : ℝ → ℝ} {a d x : ℝ}
    (hWidth : 8*a≤d) (hRight : d≤f 1) (hxLow : 1-a≤x) (hxHigh : x≤1)
    (hLip : |f x-f 1|≤4*|x-1|) : d/2≤f x := by
  have h := (abs_le.mp hLip).1
  rw [abs_of_nonpos (sub_nonpos.mpr hxHigh)] at h
  nlinarith only [h,hRight,hWidth,hxLow,hxHigh]

lemma smallMean_gap_left_slack {n : ℕ} (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hSmall : P.expectedMaximum≤1/80)
    {lam : ℝ} (hlam : lam∈Icc (0:ℝ) (4/5)) : 13/400≤normalizedScalarGap P lam := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hTime : 0≤1-lam := by linarith only [hlam.2]
  have hWait := durationWeight_le_optimalScalarValue P hP hlam.1 hTime
  have hC : optimalCompetitiveRatio≤3/4 := optimalCompetitiveRatio_le_threeQuarters
  have hCM : optimalCompetitiveRatio*P.expectedMaximum≤3/320 := by
    have h := mul_le_mul hC hSmall P.expectedMaximum_nonnegative (by norm_num : (0:ℝ)≤3/4)
    norm_num at h
    exact h
  have hCw := mul_le_mul_of_nonneg_right hC hTime
  have hCMw := mul_le_mul_of_nonneg_left hCM hlam.1
  unfold normalizedScalarGap scalarGap
  nlinarith only [hWait,hCw,hCMw,hlam.2]

/-- Full small-mean clamp with the source lower endpoint and regret multiplier5.
The upper endpoint is uniform in the instance size, laws, policy and target. -/
theorem bounded_smallMean_clamp_with_slack (mu : ℝ) (hmu : 0<mu) :
    ∃ b d0 : ℝ, b∈Ioo (4/5:ℝ) 1 ∧ 0<d0 ∧ ∀ (n : ℕ) (P : Instance n),
      (∀ i, ∀ᵐ x ∂P.law i, x≤1) → mu≤P.expectedMaximum → P.expectedMaximum≤1/80 →
      (∀ lam : ℝ, lam∈Icc (0:ℝ) 1 → lam∉Icc (4/5:ℝ) b → d0≤normalizedScalarGap P lam) ∧
      ∀ (π : RandomizedPolicy n) (lam r : ℝ), lam∈Icc (0:ℝ) 1 →
      π.normalizedRegret P (max (4/5) (min b lam))≤r →
      normalizedScalarGap P lam/40-5*r≤π.scalarObjective P lam (1-lam)-
        optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam) := by
  obtain ⟨d,hd,hSlack⟩ := bounded_reward_boundary_slack 1 mu hmu
  let a := min (1/10:ℝ) (d/8)
  let b := 1-a
  have haPos : 0<a := lt_min (by norm_num) (div_pos hd (by norm_num))
  have haBound : a≤1/10 := min_le_left _ _
  have hWidth : 8*a≤d := by
    have h := (le_div_iff₀ (by norm_num : (0:ℝ)<8)).mp (min_le_right (1/10:ℝ) (d/8))
    simpa only [a,mul_comm] using h
  have hb : b∈Ioo (4/5:ℝ) 1 := by constructor <;> dsimp only [b] <;> linarith only [haPos,haBound]
  refine ⟨b,min (13/400:ℝ) (d/2),hb,lt_min (by norm_num) (div_pos hd (by norm_num)),?_⟩
  intro n P hcap hMean hSmall
  refine ⟨?_,?_⟩
  · intro lam hlam hOutside
    have hCases : lam<4/5 ∨ b<lam := by
      simpa only [Set.mem_Icc,not_and_or,not_le] using hOutside
    rcases hCases with hLow | hHigh
    · exact (min_le_left _ _).trans (smallMean_gap_left_slack P hcap hSmall ⟨hlam.1,hLow.le⟩)
    · have hRight : d≤normalizedScalarGap P 1 := by rw [normalizedScalarGap_one];exact hSlack n P hcap hMean
      have hLip := normalizedScalarGap_weight_lipschitz_of_bounded P (H:=1) (by norm_num) hcap hlam (show (1:ℝ)∈Icc 0 1 by norm_num)
      norm_num at hLip
      exact (min_le_right _ _).trans (upper_boundary_slack hWidth hRight hHigh.le hlam.2 hLip)
  · intro π lam r hlam hRegret
    have hP := P.integrable_maximum_of_bounded hcap
    have hRho : max (4/5:ℝ) (min b lam)∈Icc (0:ℝ) 1 := by
      refine ⟨(by norm_num : (0:ℝ)≤4/5).trans (le_max_left _ _),?_⟩
      exact max_le (by norm_num) ((min_le_left _ _).trans hb.2.le)
    have hr0 : 0≤r := (π.normalizedRegret_nonnegative P hP hRho).trans hRegret
    have hF0 := normalizedScalarGap_nonnegative P hP hlam
    by_cases hLow : lam≤4/5
    · have hProj : max (4/5:ℝ) (min b lam)=4/5 := by rw [min_eq_right (hLow.trans hb.1.le),max_eq_left hLow]
      rw [hProj] at hRegret
      exact π.smallMean_lowerClamp_gap P hcap hSmall ⟨hlam.1,hLow⟩ hRegret
    · have hLow' : (4/5:ℝ)≤lam := (lt_of_not_ge hLow).le
      by_cases hHigh : lam≤b
      · have hProj : max (4/5:ℝ) (min b lam)=lam := by rw [min_eq_right hHigh,max_eq_right hLow']
        rw [hProj] at hRegret
        have hValue : normalizedScalarGap P lam-r≤π.scalarObjective P lam (1-lam)-
            optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam) := by
          unfold RandomizedPolicy.normalizedRegret at hRegret
          unfold normalizedScalarGap scalarGap
          linarith only [hRegret]
        linarith only [hValue,hF0,hr0]
      · have hbLam : b≤lam := (lt_of_not_ge hHigh).le
        have hProj : max (4/5:ℝ) (min b lam)=b := by rw [min_eq_left hbLam,max_eq_right hb.1.le]
        rw [hProj] at hRegret
        have hRight : d≤normalizedScalarGap P 1 := by rw [normalizedScalarGap_one];exact hSlack n P hcap hMean
        have hLip := normalizedScalarGap_weight_lipschitz_of_bounded P (H:=1) (by norm_num) hcap hlam (show (1:ℝ)∈Icc 0 1 by norm_num)
        norm_num at hLip
        have hCost : 2*|lam-b|≤normalizedScalarGap P lam/2 := upper_boundary_cost hWidth hRight hbLam hlam.2 hLip
        have hBUnit : b∈Icc (0:ℝ) 1 := ⟨(by norm_num : (0:ℝ)≤4/5).trans hb.1.le,hb.2.le⟩
        have hValue := π.scalarGap_ge_gap_sub_projectedRegret P (H:=1) (by norm_num) hcap hlam hBUnit hRegret
        norm_num at hValue
        linarith only [hValue,hCost,hF0,hr0]

/-- The source comparison follows from the same-interval slack package.
Its regret multiplier is the fixed number five. -/
theorem bounded_smallMean_clamp (mu : ℝ) (hmu : 0<mu) :
    ∃ b : ℝ, b∈Ioo (4/5:ℝ) 1 ∧ ∀ (n : ℕ) (P : Instance n),
      (∀ i, ∀ᵐ x ∂P.law i, x≤1) → mu≤P.expectedMaximum → P.expectedMaximum≤1/80 →
      ∀ (π : RandomizedPolicy n) (lam r : ℝ), lam∈Icc (0:ℝ) 1 →
      π.normalizedRegret P (max (4/5) (min b lam))≤r →
      normalizedScalarGap P lam/40-5*r≤π.scalarObjective P lam (1-lam)-
        optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam) := by
  obtain ⟨b,_d0,hb,_hd0,hAll⟩ := bounded_smallMean_clamp_with_slack mu hmu
  exact ⟨b,hb,fun n P hcap hMean hSmall => (hAll n P hcap hMean hSmall).2⟩

lemma smallMean_clamped_coefficient_range {b lam : ℝ} (hb : b∈Ioo (4/5:ℝ) 1) :
    let rho := max (4/5:ℝ) (min b lam)
    0<(1-b)/b ∧ (1-b)/b≤(1-rho)/rho ∧ (1-rho)/rho≤1/4 := by
  let rho := max (4/5:ℝ) (min b lam)
  have hLow : (4/5:ℝ)≤rho := le_max_left _ _
  have hHigh : rho≤b := max_le hb.1.le (min_le_left _ _)
  have hbPos : 0<b := (by norm_num : (0:ℝ)<4/5).trans hb.1
  have hRhoPos : 0<rho := (by norm_num : (0:ℝ)<4/5).trans_le hLow
  refine ⟨div_pos (sub_pos.mpr hb.2) hbPos,?_,?_⟩
  · apply (div_le_div_iff₀ hbPos hRhoPos).mpr
    nlinarith only [hHigh]
  · apply (div_le_iff₀ hRhoPos).mpr
    nlinarith only [hLow]

end ProphetSecretary.Model
