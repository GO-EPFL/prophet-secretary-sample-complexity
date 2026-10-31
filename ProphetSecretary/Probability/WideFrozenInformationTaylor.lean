import ProphetSecretary.Probability.WideFrozenTaylor
import ProphetSecretary.Probability.WideInformation

/-! # Dimension-free local Taylor remainder of a fixed policy
Re-centering changes the score information, not the fixed policy. The original
information controls this remainder uniformly throughout the half neighborhood.
-/
open MeasureTheory Set
open scoped BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

theorem RandomizedPolicy.scalarObjective_likelihoodWidePath_taylor_information
    (π : RandomizedPolicy n) (P : Instance n) {w c H : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2))
    (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hNear : |ρ - θ| ≤ 1 / 8) :
    |π.scalarObjective (P.likelihoodWidePath h hh hb hm ρ) w c -
      π.scalarObjective (P.likelihoodWidePath h hh hb hm θ) w c -
      (ρ - θ) * deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) θ| ≤
        4 * (w * H + c) * information P.law h * (ρ - θ) ^ 2 := by
  have hθ' : |θ| ≤ 1 / 2 := abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩
  let Q := P.likelihoodWideTilt h hh hb hm θ hθ'
  have hQB := P.likelihoodWideTilt_bounded h hh hb hm θ hθ' hbound
  let s := fun i ↦ recenteredUnitScore (h i) θ
  have hsM (i : Fin n) : Measurable (s i) := measurable_recenteredUnitScore (hh i) θ
  have hsB (i : Fin n) : ∀ᵐ a ∂Q.law i, |s i a| ≤ 1 := recenteredUnitScore_bound (hb i) hθ'
  have hs0 (i : Fin n) : ∫ a, s i a ∂Q.law i = 0 := recenteredUnitScore_centered (hh i) (hb i) (hm i) hθ'
  have hrel : |2 * (ρ - θ)| ≤ 1 / 4 := by rw [abs_mul]; norm_num; linarith
  have hadd : θ + (ρ - θ) = ρ := by ring
  have hRebase := P.likelihoodWideTilt_rebase h hh hb hm hθ' hrel
    (show |θ + (ρ - θ)| ≤ 1 / 2 by rw [hadd]; exact abs_le.mpr ⟨hρ.1.le, hρ.2.le⟩)
  have hRebase' : Q.likelihoodTilt s hsM hsB hs0 (2 * (ρ - θ)) hrel = P.likelihoodWidePath h hh hb hm ρ := by
    rw [P.likelihoodWidePath_of_mem h hh hb hm (abs_le.mpr ⟨hρ.1.le, hρ.2.le⟩)]
    simpa only [hadd] using hRebase
  have hBase : P.likelihoodWidePath h hh hb hm θ = Q := P.likelihoodWidePath_of_mem h hh hb hm hθ'
  have ht := π.scalarObjective_likelihood_taylor Q hH hQB hw hc s hsM hsB hs0 hrel
  change |π.scalarObjective (Q.likelihoodTilt s hsM hsB hs0 (2 * (ρ - θ)) hrel) w c - π.scalarObjective Q w c -
    (2 * (ρ - θ)) * π.scalarLikelihoodDerivative Q w c s| ≤ _ at ht
  rw [hRebase'] at ht
  rw [hBase, (π.hasDerivAt_scalarObjective_likelihoodWidePath P hw hc hH hbound h hh hb hm hθ).deriv]
  have hInfoEq : information Q.law s = (1 / 4 : ℝ) * information Q.law (fun i ↦ tiltedScore (h i) θ) := by
    unfold information
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun a ↦ by dsimp only [s, recenteredUnitScore]; ring)
  have hI : information Q.law s ≤ (1 / 2 : ℝ) * information P.law h := by
    rw [hInfoEq]
    have hi := P.information_likelihoodWideTilt_tiltedScore_le h hh hb hm hθ'
    nlinarith
  have hRem := mul_le_mul_of_nonneg_left hI
    (show 0 ≤ 2 * (w * H + c) * (2 * (ρ - θ)) ^ 2 by positivity)
  have ht' : |π.scalarObjective (P.likelihoodWidePath h hh hb hm ρ) w c - π.scalarObjective Q w c -
      (ρ - θ) * (π.scalarLikelihoodDerivative Q w c s * 2)| ≤
      2 * (w * H + c) * (2 * (ρ - θ)) ^ 2 * information Q.law s := by
    convert ht using 1
    congr 1
    ring
  apply ht'.trans
  convert hRem using 1
  ring

end ProphetSecretary.Model
