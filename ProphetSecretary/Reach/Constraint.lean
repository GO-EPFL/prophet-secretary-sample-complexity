import ProphetSecretary.Probability.JackpotCoupling

/-!
# Rare jackpots force reach

Paper correspondence: `lem:reach`. The learner is fixed before the distribution.
The base instance may have expected maximum zero; every positive-probability jackpot
perturbation has a positive finite benchmark, so the universal guarantee applies there.
The quantitative coupling error is at most `k*p` for an adaptive hard budget `k`.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

/-- A learner guaranteeing `rho*M` on all finite positive benchmarks reaches every
identity of every bounded base instance with probability at least `rho`.
The guarantee and reach probability both average over training and online randomness. -/
theorem Learner.rare_jackpot_reach {n k : ℕ} (L : Learner n k) {rho : ℝ}
    (hGuarantee : L.Guarantees rho) (P : Instance n) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H) (i : Fin n) :
    rho ≤ L.reachProbability P i := by
  by_cases hrho : rho ≤ 0
  · exact hrho.trans (L.reachProbability_nonnegative P i)
  have hrho0 : 0 ≤ rho := (lt_of_not_ge hrho).le
  apply reach_of_arbitrarily_small_jackpot_error
    (K := (k : ℝ) + H) (add_nonneg (Nat.cast_nonneg k) hH)
  intro p hp hp1
  let pp : unitInterval := ⟨p, hp.le, hp1⟩
  let A : ℝ := (p * p)⁻¹
  have hA : 0 < A := inv_pos.mpr (mul_pos hp hp)
  have hP := P.integrable_maximum_of_bounded hbound
  let Q := P.jackpot i pp A hA.le
  have hQ : Q.HasPositiveFiniteMaximum := P.jackpot_positiveFinite hP i pp hp hA
  have hprophet : (pp : ℝ) * A ≤ Q.expectedMaximum :=
    P.jackpot_expectedMaximum_ge hP i pp hA.le
  have hgood : rho * Q.expectedMaximum ≤ L.expectedReward Q := hGuarantee Q hQ
  have hupper : L.expectedReward Q ≤
      H + (pp : ℝ) * A * (L.reachProbability P i + k * (pp : ℝ)) :=
    ProphetSecretary.Probability.learner_expectedReward_jackpot_le L P i pp hH hA.le hbound
  have hineq := (mul_le_mul_of_nonneg_left hprophet hrho0).trans (hgood.trans hupper)
  have hscaled := mul_le_mul_of_nonneg_right hineq hp.le
  have hleft : rho * ((pp : ℝ) * A) * p = rho := by
    dsimp [pp, A]
    field_simp
  have hright : (H + (pp : ℝ) * A * (L.reachProbability P i + k * (pp : ℝ))) * p =
      L.reachProbability P i + ((k : ℝ) + H) * p := by
    dsimp [pp, A]
    field_simp
    ring
  rw [hleft, hright] at hscaled
  exact hscaled

end ProphetSecretary.Model
