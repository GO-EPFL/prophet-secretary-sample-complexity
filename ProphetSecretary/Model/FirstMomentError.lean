import ProphetSecretary.Model.CanonicalSelectionLower

/-!
# Error parameters in the first-moment argument

These are d_h, E₀ and e_h following `upmom:ties`. Their explicit definitions
retain dependence only on the global competitive constant and δ. The error
controls both the stationarity discrepancy and excess acceptance probability.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.valueStationarityError (P : Instance n) (δ h w c : ℝ) : ℝ :=
  scalarGap P w c / (w * h) + (32 / δ) * (1 + P.positiveCount) ^ 2 * h / w

noncomputable def firstMomentErrorFactor (δ : ℝ) : ℝ :=
  max 1 (max (2 / optimalCompetitiveRatio) (2 / δ))

noncomputable def Instance.firstMomentError (P : Instance n) (δ h w c : ℝ) : ℝ :=
  firstMomentErrorFactor δ * (P.valueStationarityError δ h w c + (1 + P.positiveCount) * h)

lemma firstMomentErrorFactor_ge_one (δ : ℝ) : 1 ≤ firstMomentErrorFactor δ := le_max_left _ _

lemma firstMomentErrorFactor_ge_two_div_delta (δ : ℝ) : 2 / δ ≤ firstMomentErrorFactor δ :=
  (le_max_right _ _).trans (le_max_right _ _)

lemma Instance.valueStationarityError_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {δ h w c : ℝ}
    (hδ : 0 < δ) (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 ≤ c) :
    0 ≤ P.valueStationarityError δ h w c := by
  unfold valueStationarityError
  exact add_nonneg (div_nonneg (scalarGap_nonnegative P hP hw.le hc) (mul_nonneg hw.le hh))
    (by positivity)

lemma Instance.acceptanceError_le_firstMomentError (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {δ h w c : ℝ}
    (hδ : 0 < δ) (hh : 0 ≤ h) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1) :
    P.valueStationarityError δ h w c + (2 * w / c) * P.positiveCount * h ≤
      P.firstMomentError δ h w c := by
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  have hw1 : w ≤ 1 := by linarith
  have hL := P.tailCount_nonnegative 0
  have hE1 := firstMomentErrorFactor_ge_one δ
  have hE2 := firstMomentErrorFactor_ge_two_div_delta δ
  have hE0 : 0 ≤ firstMomentErrorFactor δ := by linarith only [hE1]
  have hratio : 2 * w / c ≤ 2 / δ := by
    have hr := (div_le_div_of_nonneg_right hw1 hc.le).trans (one_div_le_one_div_of_le hδ hcδ)
    have hh := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * w / c = 2 * (w / c) := by ring
      _ ≤ 2 * (1 / δ) := hh
      _ = 2 / δ := by ring
  have hterm : (2 * w / c) * P.positiveCount * h ≤
      firstMomentErrorFactor δ * (1 + P.positiveCount) * h := by
    apply mul_le_mul_of_nonneg_right _ hh
    exact mul_le_mul (hratio.trans hE2) (by linarith : P.positiveCount ≤ 1 + P.positiveCount) hL hE0
  have hd := P.valueStationarityError_nonnegative hP hδ hh hw hc.le
  have hD := mul_le_mul_of_nonneg_right hE1 hd
  unfold firstMomentError
  nlinarith only [hterm, hD]

/-- The paper's per-value selection estimate under its stated e_h≤ρ condition. -/
theorem Instance.canonical_selectionAtValue_lower_of_firstMomentError (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (he : P.firstMomentError δ h w c ≤ (1 - optimalCompetitiveRatio) / 2)
    (i : Fin n) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    let ρ := (1 - optimalCompetitiveRatio) / 2
    let γ := min (ρ / 4) (δ / 2)
    (γ * ρ / 2) * a / (1 + P.totalFirstMoment) ≤
      (P.valuePolicy (P.integrable_maximum_of_bounded hcap)
        (hδ.le.trans hwδ) (hδ.le.trans hcδ)).rule.selectionProbabilityAtValue P (Measure.dirac ()) i a := by
  exact P.canonical_selectionAtValue_lower hcap hδ hwδ hcδ hsum hh hquarter
    ((P.acceptanceError_le_firstMomentError (P.integrable_maximum_of_bounded hcap)
      hδ hh.le hwδ hcδ hsum).trans he) i ha ha1

end ProphetSecretary.Model
