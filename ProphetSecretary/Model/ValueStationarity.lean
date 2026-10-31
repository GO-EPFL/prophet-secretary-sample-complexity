import ProphetSecretary.Model.ValueTransportQuadratic
import ProphetSecretary.Model.ProphetWinner
import ProphetSecretary.Reach.Robust

/-!
# Selection versus prophet response near a small scalar gap

Equation `upmom:stationarity` follows from the proved quadratic transport and
the global reward-duration inequality, applied separately to both signs. The
selection response always uses the fixed base canonical optimizer. Constants
are uniform over the finite instance size, including zero-maximum instances.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma RandomizedPolicy.selectedResponse_neg (π : RandomizedPolicy n) (P : Instance n)
    (ψ : Fin n → ℝ → ℝ) :
    π.selectedResponse P (fun i x => -ψ i x) = -π.selectedResponse P ψ := by
  unfold selectedResponse
  rw [← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    simp only [Policy.mappedReward, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp

lemma Instance.perturbValues_integrable_maximum (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) {h : ℝ} (hh : 0 ≤ h)
    (hbound : ∀ i x, |ψ i x| ≤ 1) (hsupport : ∀ i x, x < 2 * h → ψ i x = 0) :
    Integrable Instance.maximum (P.perturbValues ψ hψ hh hbound hsupport).valuesLaw := by
  apply P.mapValues_integrable_of_bounded_displacement hP
  intro i
  exact Eventually.of_forall fun x => perturbation_displacement ψ hbound h i x

lemma Instance.perturbValues_expectedMaximum_lower (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) {h : ℝ} (hh : 0 ≤ h)
    (hbound : ∀ i x, |ψ i x| ≤ 1) (hsupport : ∀ i x, x < 2 * h → ψ i x = 0) :
    P.expectedMaximum + h * P.expectedProphetResponse ψ ≤
      (P.perturbValues ψ hψ hh hbound hsupport).expectedMaximum :=
  P.expectedMaximum_perturbation_lower hP ψ hψ hbound h _

/-- The one-sided comparison before division by the positive factor wh. -/
lemma Instance.valuePerturbation_stationarity_oneSide (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) (hbound : ∀ i x, |ψ i x| ≤ 1)
    (hsupport : ∀ i x, x < 2 * h → ψ i x = 0) :
    let π := P.valuePolicy (P.integrable_maximum_of_bounded hcap)
      (hδ.le.trans hwδ) (hδ.le.trans hcδ)
    w * h * (optimalCompetitiveRatio * P.expectedProphetResponse ψ - π.selectedResponse P ψ) ≤
      scalarGap P w c + (32 / δ) * (1 + P.positiveCount) ^ 2 * h ^ 2 := by
  let Q := P.perturbValues ψ hψ hh.le hbound hsupport
  have hP := P.integrable_maximum_of_bounded hcap
  have hQ := P.perturbValues_integrable_maximum hP ψ hψ hh.le hbound hsupport
  have hR := globalScalar_inequality_of_integrable Q hQ (hδ.le.trans hwδ) (hδ.le.trans hcδ)
  have hM := P.perturbValues_expectedMaximum_lower hP ψ hψ hh.le hbound hsupport
  have htrans := (P.valuePerturbation_transport hcap hδ hwδ hcδ hsum hh hquarter ψ hψ hbound hsupport).2
  have hCm := mul_le_mul_of_nonneg_left hM
    (mul_nonneg optimalCompetitiveRatio_nonnegative (hδ.le.trans hwδ))
  dsimp only [scalarGap]
  dsimp only [Q] at hR
  nlinarith only [hR, htrans, hCm]

/-- `upmom:stationarity`, with A₀=32/δ and ℓ=1+L, for every measurable
bounded perturbation supported above 2h. -/
theorem Instance.valuePerturbation_stationarity (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) (hbound : ∀ i x, |ψ i x| ≤ 1)
    (hsupport : ∀ i x, x < 2 * h → ψ i x = 0) :
    let π := P.valuePolicy (P.integrable_maximum_of_bounded hcap)
      (hδ.le.trans hwδ) (hδ.le.trans hcδ)
    |π.selectedResponse P ψ - optimalCompetitiveRatio * P.expectedProphetResponse ψ| ≤
      scalarGap P w c / (w * h) + (32 / δ) * (1 + P.positiveCount) ^ 2 * h / w := by
  have hp := P.valuePerturbation_stationarity_oneSide hcap hδ hwδ hcδ hsum hh hquarter ψ hψ hbound hsupport
  have hn := P.valuePerturbation_stationarity_oneSide hcap hδ hwδ hcδ hsum hh hquarter
    (fun i x => -ψ i x) (fun i => (hψ i).neg)
    (fun i x => by simpa only [abs_neg] using hbound i x)
    (fun i x hx => by rw [hsupport i x hx, neg_zero])
  dsimp only at hp hn ⊢
  rw [RandomizedPolicy.selectedResponse_neg, P.expectedProphetResponse_neg] at hn
  have hw : 0 < w := hδ.trans_le hwδ
  have hwh : 0 < w * h := mul_pos hw hh
  have heq : scalarGap P w c / (w * h) + (32 / δ) * (1 + P.positiveCount) ^ 2 * h / w =
      (scalarGap P w c + (32 / δ) * (1 + P.positiveCount) ^ 2 * h ^ 2) / (w * h) := by
    field_simp
  rw [heq, abs_le]
  constructor
  · rw [mul_comm (w * h)] at hp
    have hd := (le_div_iff₀ hwh).mpr hp
    linarith only [hd]
  · apply (le_div_iff₀ hwh).mpr
    nlinarith only [hn]

end ProphetSecretary.Model
