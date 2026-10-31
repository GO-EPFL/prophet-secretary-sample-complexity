import ProphetSecretary.Model.ValueTransportExpectation
import ProphetSecretary.Model.ValuePerturbationSupport

/-!
# Quadratic transport under bounded perturbations of values

This proves `upmom:transport`, including noninjective maps. The first-order
response uses the fixed base canonical optimizer. The upper bound comes from
the actual mapped Bellman loss and independent clock integration. No positive
lower bound on the expected maximum is required.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma perturbation_nonnegative_of_support (ψ : Fin n → ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hbound : ∀ i x, |ψ i x| ≤ 1) (hsupport : ∀ i x, x < 2 * h → ψ i x = 0)
    (i : Fin n) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x + h * ψ i x := by
  by_cases hsmall : x < 2 * h
  · rw [hsupport i x hsmall, mul_zero, add_zero]
    exact hx
  · have hm := mul_le_mul_of_nonneg_left (abs_le.mp (hbound i x)).1 hh
    linarith

noncomputable def Instance.perturbValues (P : Instance n) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) {h : ℝ} (hh : 0 ≤ h)
    (hbound : ∀ i x, |ψ i x| ≤ 1) (hsupport : ∀ i x, x < 2 * h → ψ i x = 0) : Instance n :=
  P.mapValues (fun i x => x + h * ψ i x)
    (fun i => measurable_id.add (measurable_const.mul (hψ i)))
    (fun i => (P.nonnegative i).mono fun _ hx => perturbation_nonnegative_of_support ψ hh hbound hsupport i hx)

/-- Unnormalized form of the transport estimate, with all dependencies explicit. -/
theorem Instance.valuePerturbation_transport_raw (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) {h w c : ℝ} (hh : 0 < h) (hw : 0 < w) (hc : 0 < c)
    (hbound : ∀ i x, |ψ i x| ≤ 1) (hsupport : ∀ i x, x < 2 * h → ψ i x = 0) :
    let π := P.valuePolicy hP hw.le hc.le
    let remainder := optimalScalarValue (P.perturbValues ψ hψ hh.le hbound hsupport) w c -
      optimalScalarValue P w c - w * h * π.selectedResponse P ψ
    0 ≤ remainder ∧ remainder ≤
      (32 * w ^ 2 * h ^ 2 * (1 + P.positiveCount) / c) * P.positiveCount := by
  let π := P.valuePolicy hP hw.le hc.le
  let f : Fin n → ℝ → ℝ := fun i x => x + h * ψ i x
  have hf : ∀ i, Measurable (f i) := fun i => measurable_id.add (measurable_const.mul (hψ i))
  have hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x := fun i =>
    (P.nonnegative i).mono fun _ hx => perturbation_nonnegative_of_support ψ hh.le hbound hsupport i hx
  have hdispl : ∀ i x, |f i x - x| ≤ h := by
    intro i x
    simpa only [abs_of_pos hh] using perturbation_displacement ψ hbound h i x
  have hfzero : ∀ i, f i 0 = 0 := by
    intro i
    dsimp [f]
    rw [hsupport i 0 (by linarith), mul_zero, add_zero]
  have hLow := π.valuePerturbation_lower_support P hP ψ hψ hbound h hnn hw hc.le
    (P.valuePolicy_optimal hP hw hc.le)
  have hIdentity := π.mapped_bellman_loss_identity P hP f hf hnn hh.le hw hc.le hdispl
  rw [π.mappedScalarObjective_perturbation P hP ψ hψ hbound h w c,
    P.valuePolicy_optimal hP hw hc.le] at hIdentity
  have hMean := P.canonical_mappedReachedLoss_mean_bound hP f hf hnn hh.le hw hc hdispl hfzero
  have hMean' : (∫ ω : π.World, π.rule.mappedReachedLoss (P.mapValues f hf hnn) f w c
      ω.2.2 ω.1 ω.2.1 ∂P.worldLaw π.seedLaw) ≤
      (32 * w ^ 2 * h ^ 2 * (1 + P.positiveCount) / c) * P.positiveCount := by
    dsimp only [π, Instance.valuePolicy]
    convert hMean using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      rcases ω with ⟨x, u, r⟩
      cases r
      rfl
  constructor
  · change 0 ≤ optimalScalarValue (P.mapValues f hf hnn) w c - optimalScalarValue P w c - w * h * π.selectedResponse P ψ
    linarith only [hLow]
  · change optimalScalarValue (P.mapValues f hf hnn) w c - optimalScalarValue P w c - w * h * π.selectedResponse P ψ ≤ _
    linarith only [hIdentity, hMean']

/-- `upmom:transport` with the manuscript's constant A₀=32/δ and ℓ=1+L. -/
theorem Instance.valuePerturbation_transport (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (_hquarter : h ≤ 1 / 4) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) (hbound : ∀ i x, |ψ i x| ≤ 1)
    (hsupport : ∀ i x, x < 2 * h → ψ i x = 0) :
    let hP := P.integrable_maximum_of_bounded hcap
    let π := P.valuePolicy hP (hδ.le.trans hwδ) (hδ.le.trans hcδ)
    let remainder := optimalScalarValue (P.perturbValues ψ hψ hh.le hbound hsupport) w c -
      optimalScalarValue P w c - w * h * π.selectedResponse P ψ
    0 ≤ remainder ∧ remainder ≤ (32 / δ) * (1 + P.positiveCount) ^ 2 * h ^ 2 := by
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  have hraw := P.valuePerturbation_transport_raw (P.integrable_maximum_of_bounded hcap) ψ hψ hh hw hc hbound hsupport
  refine ⟨hraw.1, hraw.2.trans ?_⟩
  have hL : 0 ≤ P.positiveCount := P.tailCount_nonnegative 0
  have hw1 : w ≤ 1 := by linarith
  have hw2 : w ^ 2 ≤ 1 := by nlinarith
  have hratio : w ^ 2 / c ≤ 1 / δ :=
    (div_le_div_of_nonneg_right hw2 hc.le).trans (one_div_le_one_div_of_le hδ hcδ)
  have hcounts : (1 + P.positiveCount) * P.positiveCount ≤ (1 + P.positiveCount) ^ 2 := by nlinarith
  have hprod := mul_le_mul hratio hcounts
    (mul_nonneg (by linarith : 0 ≤ 1 + P.positiveCount) hL) (by positivity : (0 : ℝ) ≤ 1 / δ)
  have hfinal := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 32 * h ^ 2)
  convert hfinal using 1 <;> ring

end ProphetSecretary.Model
