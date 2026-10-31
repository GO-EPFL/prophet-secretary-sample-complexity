import ProphetSecretary.Probability.WidePolicyLikelihood

/-!
# Finite quadratic Taylor bounds for a fixed policy under law changes

Local re-centering gives the actual product-score Taylor remainder. A common
Lipschitz bound covers larger displacements in the wider half interval. The
policy, its auxiliary law, and all decisions remain fixed during differentiation.
-/

open MeasureTheory Set
open scoped Topology

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem RandomizedPolicy.scalarObjective_likelihoodWidePath_taylor (π : RandomizedPolicy n) (P : Instance n)
    {w c H : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    |π.scalarObjective (P.likelihoodWidePath h hh hb hm ρ) w c - π.scalarObjective (P.likelihoodWidePath h hh hb hm θ) w c -
      (ρ - θ) * deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) θ| ≤
        (32 * (w * H + c) * (n : ℝ)) * (ρ - θ) ^ 2 := by
  let U := w * H + c
  have hU : 0 ≤ U := add_nonneg (mul_nonneg hw hH) hc
  by_cases hnear : |ρ - θ| ≤ 1 / 8
  · let hθ' := abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩
    let Q := P.likelihoodWideTilt h hh hb hm θ hθ'
    have hQB := P.likelihoodWideTilt_bounded h hh hb hm θ hθ' hbound
    let s := fun i ↦ recenteredUnitScore (h i) θ
    have hsM (i : Fin n) : Measurable (s i) := measurable_recenteredUnitScore (hh i) θ
    have hsB (i : Fin n) : ∀ᵐ a ∂Q.law i, |s i a| ≤ 1 := recenteredUnitScore_bound (hb i) hθ'
    have hs0 (i : Fin n) : ∫ a, s i a ∂Q.law i = 0 := recenteredUnitScore_centered (hh i) (hb i) (hm i) hθ'
    have hrel : |2 * (ρ - θ)| ≤ 1 / 4 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
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
    have hI := information_le_card Q.law s hsM hsB
    have hN := mul_le_mul_of_nonneg_left hI (show 0 ≤ 2 * U * (2 * (ρ - θ)) ^ 2 by positivity)
    have hrem : 2 * U * (2 * (ρ - θ)) ^ 2 * information Q.law s ≤ (32 * U * (n : ℝ)) * (ρ - θ) ^ 2 := by
      have h0 := mul_nonneg (mul_nonneg hU (Nat.cast_nonneg n)) (sq_nonneg (ρ - θ))
      nlinarith
    apply le_trans ?_ hrem
    dsimp only [Q, s] at ht ⊢
    convert ht using 1
    congr 1
    ring
  · have hL := π.scalarObjective_likelihoodWidePath_lipschitz P hw hc hH hbound h hh hb hm hθ hρ
    have hD := π.abs_deriv_scalarObjective_likelihoodWidePath_le P hw hc hH hbound h hh hb hm hθ
    have hsquare : |ρ - θ| ≤ 8 * (ρ - θ) ^ 2 := by
      have hp := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hnear)) (abs_nonneg (ρ - θ))
      nlinarith [sq_abs (ρ - θ)]
    calc
      _ ≤ |π.scalarObjective (P.likelihoodWidePath h hh hb hm ρ) w c - π.scalarObjective (P.likelihoodWidePath h hh hb hm θ) w c| +
          |(ρ - θ) * deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) θ| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (π.scalarObjective (P.likelihoodWidePath h hh hb hm ρ) w c -
            π.scalarObjective (P.likelihoodWidePath h hh hb hm θ) w c) 0
            ((ρ - θ) * deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) θ))
      _ ≤ (2 * U * (n : ℝ)) * |ρ - θ| + |ρ - θ| * (2 * U * (n : ℝ)) := by
        rw [abs_mul]
        exact add_le_add hL (mul_le_mul_of_nonneg_left hD (abs_nonneg _))
      _ = (4 * U * (n : ℝ)) * |ρ - θ| := by ring
      _ ≤ (4 * U * (n : ℝ)) * (8 * (ρ - θ) ^ 2) := mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = _ := by ring

end ProphetSecretary.Model
