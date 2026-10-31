import ProphetSecretary.Probability.WideLikelihoodPath
import ProphetSecretary.Probability.PolicyLikelihoodDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Fixed-payoff calculus and finite law Lipschitz bounds

Every general policy remains fixed while the product laws vary. Its derivative
bound is uniform over that policy, so taking the supremum gives a finite-instance
law Lipschitz bound even when the duration coefficient is zero.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace ProphetSecretary.Probability

lemma information_le_card {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂μ i, |h i a| ≤ 1) : information μ h ≤ (n : ℝ) := by
  unfold information
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ ↦ by
      have hi := integral_mono_ae (integrable_pow_of_bound (hh i) zero_le_one (hb i) 2)
        (integrable_const (1 : ℝ)) ((hb i).mono (fun a ha ↦ (sq_le_one_iff_abs_le_one (h i a)).mpr ha))
      simpa only [integral_const, probReal_univ, one_smul] using hi)
    _ = _ := by simp

end ProphetSecretary.Probability

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem RandomizedPolicy.hasDerivAt_scalarObjective_likelihoodWidePath (π : RandomizedPolicy n) (P : Instance n)
    {w c H : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    let Q := P.likelihoodWideTilt h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩)
    HasDerivAt (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c)
      (π.scalarLikelihoodDerivative Q w c (fun i ↦ recenteredUnitScore (h i) θ) * 2) θ := by
  let hθ' := abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩
  let Q := P.likelihoodWideTilt h hh hb hm θ hθ'
  have hQBound := P.likelihoodWideTilt_bounded h hh hb hm θ hθ' hbound
  let s := fun i ↦ recenteredUnitScore (h i) θ
  have hsM (i : Fin n) : Measurable (s i) := measurable_recenteredUnitScore (hh i) θ
  have hsB (i : Fin n) : ∀ᵐ a ∂Q.law i, |s i a| ≤ 1 := recenteredUnitScore_bound (hb i) hθ'
  have hs0 (i : Fin n) : ∫ a, s i a ∂Q.law i = 0 := recenteredUnitScore_centered (hh i) (hb i) (hm i) hθ'
  let L := π.scalarLikelihoodDerivative Q w c s
  have hD := π.hasDerivAt_scalarObjective_likelihoodPath Q hH hQBound hw hc s hsM hsB hs0
  have hInner : HasDerivAt (fun t : ℝ ↦ 2 * (t - θ)) 2 θ := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id θ).sub_const θ).const_mul 2
  have hD' : HasDerivAt (fun δ ↦ π.scalarObjective (Q.likelihoodPath s hsM hsB hs0 δ) w c) L (2 * (θ - θ)) := by
    simpa only [sub_self, mul_zero] using hD
  apply (hD'.comp θ hInner).congr_of_eventuallyEq
  have hnear : ∀ᶠ t : ℝ in 𝓝 θ,
      t ∈ Icc (-(1 / 2) : ℝ) (1 / 2) ∧ |2 * (t - θ)| ≤ 1 / 4 := by
    have hclose : ∀ᶠ t : ℝ in 𝓝 θ, t ∈ Icc (θ - 1 / 8) (θ + 1 / 8) :=
      Icc_mem_nhds (by linarith) (by linarith)
    filter_upwards [Icc_mem_nhds hθ.1 hθ.2, hclose] with t ht ht'
    exact ⟨ht, abs_le.mpr ⟨by linarith [ht'.1], by linarith [ht'.2]⟩⟩
  filter_upwards [hnear] with t ht
  have hAbsT : |t| ≤ 1 / 2 := abs_le.mpr ⟨ht.1.1, ht.1.2⟩
  dsimp only [Function.comp_apply]
  rw [P.likelihoodWidePath_of_mem h hh hb hm hAbsT, Q.likelihoodPath_of_mem s hsM hsB hs0 ht.2]
  have hadd : θ + (t - θ) = t := by ring
  have he := P.likelihoodWideTilt_rebase h hh hb hm hθ' ht.2
    (show |θ + (t - θ)| ≤ 1 / 2 by simpa only [hadd] using hAbsT)
  have he' : Q.likelihoodTilt s hsM hsB hs0 (2 * (t - θ)) ht.2 =
      P.likelihoodWideTilt h hh hb hm t hAbsT := by simpa only [hadd] using he
  rw [he']

lemma RandomizedPolicy.abs_deriv_scalarObjective_likelihoodWidePath_le (π : RandomizedPolicy n) (P : Instance n)
    {w c H : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    |deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) θ| ≤
      2 * (w * H + c) * (n : ℝ) := by
  rw [(π.hasDerivAt_scalarObjective_likelihoodWidePath P hw hc hH hbound h hh hb hm hθ).deriv, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hs := π.scalarLikelihoodDerivative_bound
    (P.likelihoodWideTilt h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩)) hH
    (P.likelihoodWideTilt_bounded h hh hb hm θ _ hbound) hw hc
    (fun i ↦ recenteredUnitScore (h i) θ) (fun i ↦ recenteredUnitScore_bound (hb i) (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩))
  nlinarith

lemma RandomizedPolicy.scalarObjective_likelihoodWidePath_lipschitz (π : RandomizedPolicy n) (P : Instance n)
    {w c H : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    |π.scalarObjective (P.likelihoodWidePath h hh hb hm ρ) w c - π.scalarObjective (P.likelihoodWidePath h hh hb hm θ) w c| ≤
      (2 * (w * H + c) * (n : ℝ)) * |ρ - θ| := by
  have hM := (convex_Ioo (-(1 / 2) : ℝ) (1 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht ↦ (π.hasDerivAt_scalarObjective_likelihoodWidePath P hw hc hH hbound h hh hb hm ht).differentiableAt.hasDerivAt.hasDerivWithinAt)
    (fun t ht ↦ by simpa only [Real.norm_eq_abs] using π.abs_deriv_scalarObjective_likelihoodWidePath_le P hw hc hH hbound h hh hb hm ht) hθ hρ
  simpa only [Real.norm_eq_abs] using hM

/-- Supremum over all randomized policies preserves the common finite law
Lipschitz constant, including zero duration weight. -/
theorem Instance.optimalScalarValue_likelihoodWidePath_lipschitz (P : Instance n)
    {w c H : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    |optimalScalarValue (P.likelihoodWidePath h hh hb hm ρ) w c -
        optimalScalarValue (P.likelihoodWidePath h hh hb hm θ) w c| ≤
      (2 * (w * H + c) * (n : ℝ)) * |ρ - θ| := by
  have hDir (s t : ℝ) (hs : s ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
      optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c ≤
        optimalScalarValue (P.likelihoodWidePath h hh hb hm s) w c +
          (2 * (w * H + c) * (n : ℝ)) * |t - s| := by
    apply csSup_le (scalarValues_nonempty _ w c)
    rintro v ⟨π, rfl⟩
    have hL := π.scalarObjective_likelihoodWidePath_lipschitz P hw hc hH hbound h hh hb hm hs ht
    have hV := scalarObjective_le_optimal π (P.likelihoodWidePath h hh hb hm s)
      ((P.likelihoodWidePath h hh hb hm s).integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm s hbound)) hw hc
    linarith [le_abs_self (π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c - π.scalarObjective (P.likelihoodWidePath h hh hb hm s) w c)]
  rw [abs_le]
  have h1 := hDir θ ρ hθ hρ
  have h2 := hDir ρ θ hρ hθ
  rw [abs_sub_comm θ ρ] at h2
  constructor <;> linarith

end ProphetSecretary.Model
