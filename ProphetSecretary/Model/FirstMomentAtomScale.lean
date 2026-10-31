import ProphetSecretary.Model.MaximumAtomTies
import ProphetSecretary.Model.FirstMomentConstants

/-!
# Aggregate atom control above the first-moment scale

The scale constant K depends only on δ and the global competitive ratio.
The atom comparison, tied-maximum estimate and actual selection lower bound
show every aggregate atom above a*=K(1+S)e_h has mass less than two. The
argument never divides by e_h, and the scale remains valid when the scalar
gap is zero.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def firstMomentAtomScaleConstant (δ : ℝ) : ℝ :=
  max 2 (max ((6 * optimalCompetitiveRatio + 1) / firstMomentSelectionConstant δ)
    (2 / firstMomentSelectionConstant δ))

lemma firstMomentAtomScaleConstant_ge_two (δ : ℝ) : 2 ≤ firstMomentAtomScaleConstant δ := le_max_left _ _
lemma firstMomentAtomScaleConstant_ge_atomRatio (δ : ℝ) :
    (6 * optimalCompetitiveRatio + 1) / firstMomentSelectionConstant δ ≤ firstMomentAtomScaleConstant δ :=
  (le_max_left _ _).trans (le_max_right _ _)
lemma firstMomentAtomScaleConstant_ge_two_div_selection (δ : ℝ) :
    2 / firstMomentSelectionConstant δ ≤ firstMomentAtomScaleConstant δ :=
  (le_max_right _ _).trans (le_max_right _ _)

lemma Instance.firstMomentError_ge_stationarity (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {δ h w c : ℝ}
    (hδ : 0 < δ) (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 ≤ c) :
    P.valueStationarityError δ h w c ≤ P.firstMomentError δ h w c := by
  have hd := P.valueStationarityError_nonnegative hP hδ hh hw hc
  have hL : 0 ≤ P.positiveCount := P.tailCount_nonnegative 0
  have hE := firstMomentErrorFactor_ge_one δ
  have hsum : 0 ≤ P.valueStationarityError δ h w c + (1 + P.positiveCount) * h := by positivity
  have hm := mul_le_mul_of_nonneg_right hE hsum
  unfold firstMomentError
  nlinarith only [hm, mul_nonneg (by linarith : 0 ≤ 1 + P.positiveCount) hh]

lemma Instance.firstMomentError_ge_step (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {δ h w c : ℝ}
    (hδ : 0 < δ) (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 ≤ c) :
    h ≤ P.firstMomentError δ h w c := by
  have hd := P.valueStationarityError_nonnegative hP hδ hh hw hc
  have hL : 0 ≤ P.positiveCount := P.tailCount_nonnegative 0
  have hE := firstMomentErrorFactor_ge_one δ
  have hsum : 0 ≤ P.valueStationarityError δ h w c + (1 + P.positiveCount) * h := by positivity
  have hm := mul_le_mul_of_nonneg_right hE hsum
  unfold firstMomentError
  nlinarith only [hm, hd, mul_nonneg hL hh]

lemma Instance.firstMomentError_positive (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {δ h w c : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) (hw : 0 < w) (hc : 0 ≤ c) :
    0 < P.firstMomentError δ h w c :=
  hh.trans_le (P.firstMomentError_ge_step hP hδ hh.le hw hc)

noncomputable def Instance.firstMomentAtomScale (P : Instance n) (δ h w c : ℝ) : ℝ :=
  firstMomentAtomScaleConstant δ * (1 + P.totalFirstMoment) * P.firstMomentError δ h w c

/-- The scale a* is at least 2h, including when the scalar gap is zero. -/
theorem Instance.firstMomentAtomScale_ge_two_steps (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {δ h w c : ℝ}
    (hδ : 0 < δ) (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 ≤ c) :
    2 * h ≤ P.firstMomentAtomScale δ h w c := by
  have he := P.firstMomentError_ge_step hP hδ hh hw hc
  have he0 : 0 ≤ P.firstMomentError δ h w c := hh.trans he
  have hS := P.totalFirstMoment_nonnegative
  have hK := firstMomentAtomScaleConstant_ge_two δ
  have hKD : 2 ≤ firstMomentAtomScaleConstant δ * (1 + P.totalFirstMoment) := by nlinarith only [hK,hS]
  have hm := mul_le_mul_of_nonneg_right hKD he0
  unfold firstMomentAtomScale
  linarith only [hm,he]

lemma Instance.firstMomentAtomScale_positive (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {δ h w c : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) (hw : 0 < w) (hc : 0 ≤ c) :
    0 < P.firstMomentAtomScale δ h w c :=
  (by positivity : (0 : ℝ) < 2 * h).trans_le (P.firstMomentAtomScale_ge_two_steps hP hδ hh.le hw hc)

/-- The aggregate atom cap in the paragraph following `upmom:atomeq`.
No division by e_h is used; positive h itself excludes the degenerate e_h=0. -/
theorem Instance.aggregateAtomMass_lt_two_above_scale (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (he : P.firstMomentError δ h w c ≤ firstMomentSurvivalConstant)
    {a : ℝ} (hscale : P.firstMomentAtomScale δ h w c ≤ a) (ha1 : a ≤ 1) :
    P.aggregateAtomMass a < 2 := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  have ha2h := (P.firstMomentAtomScale_ge_two_steps hP hδ hh.le hw hc.le).trans hscale
  have ha0 : 0 < a := by linarith only [ha2h,hh]
  have hκ := firstMomentSelectionConstant_positive hδ
  have hS := P.totalFirstMoment_nonnegative
  have hden : 0 < 1 + P.totalFirstMoment := by linarith only [hS]
  have hD := P.firstMomentError_ge_stationarity hP hδ hh.le hw hc.le
  have he0 : 0 ≤ P.firstMomentError δ h w c := hh.le.trans (P.firstMomentError_ge_step hP hδ hh.le hw hc.le)
  by_contra hmass
  have hmass2 : 2 ≤ P.aggregateAtomMass a := not_lt.mp hmass
  have hAtom := P.maximum_atom_le_six_tied_atom ha0 hmass2
  have hsub : {x : Fin n → ℝ | Instance.maximum x = a ∧ MaximumTiedAtLeast a x} ⊆
      {x : Fin n → ℝ | MaximumTiedAtLeast (2 * h) x} := by
    intro x hx
    exact ⟨ha2h.trans hx.2.1, hx.2.2⟩
  have hTie := (measureReal_mono hsub (μ := P.valuesLaw)).trans
    (P.maximum_tie_probability_le_firstMomentError hcap hδ hwδ hcδ hsum hh hquarter)
  have hAtomBound : P.valuesLaw.real {x : Fin n → ℝ | Instance.maximum x = a} ≤
      6 * P.firstMomentError δ h w c :=
    hAtom.trans (mul_le_mul_of_nonneg_left hTie (by norm_num))
  have hA := P.canonical_aggregateAtom_bound hcap hδ hwδ hcδ hsum hh hquarter he ha2h ha1
  change (firstMomentSelectionConstant δ * a / (1 + P.totalFirstMoment)) * P.aggregateAtomMass a ≤ _ at hA
  have hC := optimalCompetitiveRatio_nonnegative
  have hupper := mul_le_mul_of_nonneg_left hAtomBound hC
  have hb0 : 0 ≤ firstMomentSelectionConstant δ * a / (1 + P.totalFirstMoment) := by positivity
  have hLower := mul_le_mul_of_nonneg_left hmass2 hb0
  have h2 : 2 * (firstMomentSelectionConstant δ * a / (1 + P.totalFirstMoment)) ≤
      (6 * optimalCompetitiveRatio + 1) * P.firstMomentError δ h w c := by
    nlinarith only [hLower,hA,hupper,hD]
  have hdiv : (2 * firstMomentSelectionConstant δ * a) / (1 + P.totalFirstMoment) ≤
      (6 * optimalCompetitiveRatio + 1) * P.firstMomentError δ h w c := by
    convert h2 using 1; ring
  have hmain := (div_le_iff₀ hden).mp hdiv
  have hK := (div_le_iff₀ hκ).mp (firstMomentAtomScaleConstant_ge_atomRatio δ)
  have hcoeff := mul_le_mul_of_nonneg_right hK (mul_nonneg he0 hden.le)
  have hscaled := mul_le_mul_of_nonneg_left hscale hκ.le
  change firstMomentSelectionConstant δ *
      (firstMomentAtomScaleConstant δ * (1 + P.totalFirstMoment) * P.firstMomentError δ h w c) ≤
      firstMomentSelectionConstant δ * a at hscaled
  have hpos : 0 < firstMomentSelectionConstant δ * a := mul_pos hκ ha0
  nlinarith only [hmain,hcoeff,hscaled,hpos]

end ProphetSecretary.Model
