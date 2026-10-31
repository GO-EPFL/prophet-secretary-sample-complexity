import ProphetSecretary.Model.FirstMomentAtomScale

/-!
# Explicit scale choice for the first-moment theorem

The constants and the positive gap radius depend only on δ and the global
competitive ratio. The bound retains the paper's powers of ℓ=1+L and the
positive perturbation scale even when the scalar gap vanishes.
-/
open MeasureTheory Set
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def firstMomentScaleErrorConstant (δ : ℝ) : ℝ :=
  firstMomentErrorFactor δ * ((1 + 32 / δ) / δ + 1)

lemma firstMomentScaleErrorConstant_positive {δ : ℝ} (hδ : 0 < δ) :
    0 < firstMomentScaleErrorConstant δ := by
  have hE : 0 < firstMomentErrorFactor δ := zero_lt_one.trans_le (firstMomentErrorFactor_ge_one δ)
  unfold firstMomentScaleErrorConstant
  positivity

noncomputable def firstMomentPerturbationRadius (δ : ℝ) : ℝ :=
  min (1 / 4) (min (firstMomentSurvivalConstant / firstMomentScaleErrorConstant δ)
    (1 / (4 * firstMomentAtomScaleConstant δ * firstMomentScaleErrorConstant δ)))
noncomputable def firstMomentGapRadius (δ : ℝ) : ℝ := firstMomentPerturbationRadius δ ^ 2

lemma firstMomentPerturbationRadius_positive {δ : ℝ} (hδ : 0 < δ) :
    0 < firstMomentPerturbationRadius δ := by
  have hK1 := firstMomentScaleErrorConstant_positive hδ
  have hρ := firstMomentSurvivalConstant_positive
  have hK : 0 < firstMomentAtomScaleConstant δ := (by norm_num : (0 : ℝ) < 2).trans_le (firstMomentAtomScaleConstant_ge_two δ)
  unfold firstMomentPerturbationRadius
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

lemma firstMomentGapRadius_positive {δ : ℝ} (hδ : 0 < δ) : 0 < firstMomentGapRadius δ :=
  sq_pos_of_pos (firstMomentPerturbationRadius_positive hδ)

/-- The source scale estimate e_h≤K₁ t/ℓ for F≤t²ℓ⁻⁴ and h=tℓ⁻³. -/
theorem Instance.firstMomentError_le_scaled_radius (P : Instance n)
    {δ t w c : ℝ} (hδ : 0 < δ) (ht : 0 < t) (hwδ : δ ≤ w)
    (hgap : scalarGap P w c ≤ t ^ 2 / (1 + P.positiveCount) ^ 4) :
    P.firstMomentError δ (t / (1 + P.positiveCount) ^ 3) w c ≤
      firstMomentScaleErrorConstant δ * t / (1 + P.positiveCount) := by
  let ℓ := 1 + P.positiveCount
  let A₀ := 32 / δ
  have hL : 0 ≤ P.positiveCount := P.tailCount_nonnegative 0
  have hℓ1 : 1 ≤ ℓ := by dsimp [ℓ]; linarith only [hL]
  have hℓ : 0 < ℓ := by linarith only [hℓ1]
  have hw : 0 < w := hδ.trans_le hwδ
  have hA : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hE : 0 ≤ firstMomentErrorFactor δ := zero_le_one.trans (firstMomentErrorFactor_ge_one δ)
  have hinv := one_div_le_one_div_of_le hδ hwδ
  have hquot : t / (w * ℓ) ≤ t / (δ * ℓ) := by
    have h := mul_le_mul_of_nonneg_left hinv (div_nonneg ht.le hℓ.le)
    calc
      _ = (t / ℓ) * (1 / w) := by field_simp [hw.ne',hℓ.ne']
      _ ≤ (t / ℓ) * (1 / δ) := h
      _ = _ := by field_simp [hδ.ne',hℓ.ne']
  have h1 : scalarGap P w c / (w * (t / ℓ ^ 3)) ≤ t / (δ * ℓ) := by
    calc
      _ ≤ (t ^ 2 / ℓ ^ 4) / (w * (t / ℓ ^ 3)) :=
        div_le_div_of_nonneg_right hgap (by positivity)
      _ = t / (w * ℓ) := by field_simp [hw.ne',hℓ.ne',ht.ne']
      _ ≤ _ := hquot
  have h2 : A₀ * ℓ ^ 2 * (t / ℓ ^ 3) / w ≤ A₀ * t / (δ * ℓ) := by
    have hm := mul_le_mul_of_nonneg_left hquot hA
    calc
      _ = A₀ * (t / (w * ℓ)) := by field_simp [hw.ne',hℓ.ne']
      _ ≤ A₀ * (t / (δ * ℓ)) := hm
      _ = _ := by ring
  have h3 : ℓ * (t / ℓ ^ 3) ≤ t / ℓ := by
    have hpow : ℓ ≤ ℓ ^ 2 := by nlinarith only [hℓ1]
    have hh := mul_le_mul_of_nonneg_left hpow ht.le
    have hdiv : t / ℓ ^ 2 ≤ t / ℓ := (div_le_div_iff₀ (sq_pos_of_pos hℓ) hℓ).mpr hh
    have heq : ℓ * (t / ℓ ^ 3) = t / ℓ ^ 2 := by field_simp [hℓ.ne']
    rw [heq]
    exact hdiv
  change firstMomentErrorFactor δ * (scalarGap P w c / (w * (t / ℓ ^ 3)) +
    A₀ * ℓ ^ 2 * (t / ℓ ^ 3) / w + ℓ * (t / ℓ ^ 3)) ≤ _
  calc
    _ ≤ firstMomentErrorFactor δ * (t / (δ * ℓ) + A₀ * t / (δ * ℓ) + t / ℓ) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) hE
    _ = _ := by
      unfold firstMomentScaleErrorConstant
      dsimp [A₀,ℓ]
      field_simp [hδ.ne',hℓ.ne']

lemma sqrt_firstMomentGapRadius {δ : ℝ} (hδ : 0 < δ) :
    Real.sqrt (firstMomentGapRadius δ) = firstMomentPerturbationRadius δ :=
  Real.sqrt_sq (firstMomentPerturbationRadius_positive hδ).le

/-- The explicit positive radius simultaneously supplies all three scale
conditions used to absorb the integrated first-moment estimate. No bound on
S or positive lower bound on the expected maximum is a premise. -/
theorem Instance.firstMoment_scale_choice (P : Instance n) {δ w c : ℝ}
    (hδ : 0 < δ) (hwδ : δ ≤ w)
    (hgap : scalarGap P w c ≤ firstMomentGapRadius δ / (1 + P.positiveCount) ^ 4) :
    let h := Real.sqrt (firstMomentGapRadius δ) / (1 + P.positiveCount) ^ 3
    0 < h ∧ h ≤ 1 / 4 ∧ P.firstMomentError δ h w c ≤ firstMomentSurvivalConstant ∧
      firstMomentAtomScaleConstant δ * P.positiveCount * P.firstMomentError δ h w c ≤ 1 / 4 := by
  let ℓ := 1 + P.positiveCount
  let t := firstMomentPerturbationRadius δ
  let K₁ := firstMomentScaleErrorConstant δ
  let K := firstMomentAtomScaleConstant δ
  have hL : 0 ≤ P.positiveCount := P.tailCount_nonnegative 0
  have hℓ1 : 1 ≤ ℓ := by dsimp [ℓ]; linarith only [hL]
  have hℓ : 0 < ℓ := by linarith only [hℓ1]
  have ht : 0 < t := firstMomentPerturbationRadius_positive hδ
  have hK₁ : 0 < K₁ := firstMomentScaleErrorConstant_positive hδ
  have hK : 0 < K := (by norm_num : (0 : ℝ) < 2).trans_le (firstMomentAtomScaleConstant_ge_two δ)
  have htquarter : t ≤ 1 / 4 := min_le_left _ _
  have htρ : t ≤ firstMomentSurvivalConstant / K₁ := (min_le_right _ _).trans (min_le_left _ _)
  have htK : t ≤ 1 / (4 * K * K₁) := (min_le_right _ _).trans (min_le_right _ _)
  have he := P.firstMomentError_le_scaled_radius hδ ht hwδ hgap
  change P.firstMomentError δ (t / ℓ ^ 3) w c ≤ K₁ * t / ℓ at he
  have hpow : 1 ≤ ℓ ^ 3 := one_le_pow₀ hℓ1
  have hstep : t / ℓ ^ 3 ≤ t := by
    apply (div_le_iff₀ (by positivity : 0 < ℓ ^ 3)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow ht.le
  have heρ : P.firstMomentError δ (t / ℓ ^ 3) w c ≤ firstMomentSurvivalConstant := by
    have hquot : K₁ * t / ℓ ≤ K₁ * t := by
      apply (div_le_iff₀ hℓ).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hℓ1 (mul_nonneg hK₁.le ht.le)
    have hsmall := (le_div_iff₀ hK₁).mp htρ
    nlinarith only [he,hquot,hsmall]
  have hKL : K * P.positiveCount * P.firstMomentError δ (t / ℓ ^ 3) w c ≤ 1 / 4 := by
    have hm := mul_le_mul_of_nonneg_left he (mul_nonneg hK.le hL)
    have hfrac : K * P.positiveCount * (K₁ * t / ℓ) ≤ K * K₁ * t := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hℓ).mpr
      have hcount : P.positiveCount ≤ ℓ := by dsimp [ℓ]; linarith
      have hprod := mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ K * K₁ * t)
      convert hprod using 1; ring
    have hsmall := (le_div_iff₀ (by positivity : 0 < 4 * K * K₁)).mp htK
    nlinarith only [hm,hfrac,hsmall]
  dsimp only
  rw [sqrt_firstMomentGapRadius hδ]
  exact ⟨by positivity, hstep.trans htquarter, heρ, hKL⟩

end ProphetSecretary.Model
