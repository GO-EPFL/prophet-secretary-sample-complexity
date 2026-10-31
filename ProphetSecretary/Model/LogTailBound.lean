import ProphetSecretary.Model.LogTailFromAtomCap
import ProphetSecretary.Model.FirstMomentAtomScale

/-!
# The logarithmic tail-count estimate

This assembles `upmom:logtail` with K₀=max(e,2Ce/κ), the actual aggregate atom
cap, and the proved high-tail discrepancy bound. All prerequisites are proved
for the finite instance; no atom-cap or marginal-probability assumption remains.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def firstMomentLogTailConstant (δ : ℝ) : ℝ :=
  max (Real.exp 1) (2 * optimalCompetitiveRatio * Real.exp 1 / firstMomentSelectionConstant δ)

lemma firstMomentLogTailConstant_positive (δ : ℝ) : 0 < firstMomentLogTailConstant δ :=
  (Real.exp_pos 1).trans_le (le_max_left _ _)

/-- `upmom:logtail`, uniform in the finite number of independent offers. -/
theorem Instance.logarithmic_tailCount_bound (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (he : P.firstMomentError δ h w c ≤ firstMomentSurvivalConstant)
    {a : ℝ} (hscale : P.firstMomentAtomScale δ h w c ≤ a) (ha1 : a ≤ 1) :
    (∑ i, (P.law i).real (Ici a)) ≤
      Real.log (firstMomentLogTailConstant δ * (1 + P.totalFirstMoment) / a) + 3 := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  have hS := P.totalFirstMoment_nonnegative
  have hκ := firstMomentSelectionConstant_positive hδ
  have hK := firstMomentLogTailConstant_positive δ
  have ha2h := (P.firstMomentAtomScale_ge_two_steps hP hδ hh.le hw hc.le).trans hscale
  have ha0 : 0 < a := by linarith only [ha2h, hh]
  have hD := P.firstMomentError_ge_stationarity hP hδ hh.le hw hc.le
  have he0 : 0 ≤ P.firstMomentError δ h w c := hh.le.trans (P.firstMomentError_ge_step hP hδ hh.le hw hc.le)
  have hKs := (div_le_iff₀ hκ).mp (firstMomentAtomScaleConstant_ge_two_div_selection δ)
  have hde := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 2 * (1 + P.totalFirstMoment))
  have hmul := mul_le_mul_of_nonneg_right hKs
    (mul_nonneg (by positivity : 0 ≤ 1 + P.totalFirstMoment) he0)
  have hA := mul_le_mul_of_nonneg_left hscale hκ.le
  unfold Instance.firstMomentAtomScale at hA
  have hsmall : 2 * (1 + P.totalFirstMoment) * P.valueStationarityError δ h w c ≤
      firstMomentSelectionConstant δ * a := by nlinarith only [hde, hmul, hA]
  have hK1 : 1 ≤ firstMomentLogTailConstant δ := by
    have hexp := Real.add_one_le_exp (1 : ℝ)
    exact (by linarith only [hexp] : (1 : ℝ) ≤ Real.exp 1).trans (le_max_left _ _)
  have hR : 1 ≤ firstMomentLogTailConstant δ * (1 + P.totalFirstMoment) / a := by
    apply hK1.trans
    apply (le_div_iff₀ ha0).mpr
    have hfactor : a ≤ 1 + P.totalFirstMoment := by linarith only [ha1, hS]
    exact mul_le_mul_of_nonneg_left hfactor hK.le
  have hlog : 0 ≤ Real.log (firstMomentLogTailConstant δ * (1 + P.totalFirstMoment) / a) + 2 :=
    by linarith only [Real.log_nonneg hR]
  exact P.logtail_of_atomCap hcap hδ hwδ hcδ hsum hh hquarter he ha2h hK
    (le_max_right _ _) hsmall hlog
    (fun x hx => P.aggregateAtomMass_lt_two_above_scale hcap hδ hwδ hcδ hsum hh hquarter he
      (hscale.trans hx.1) hx.2)

end ProphetSecretary.Model
