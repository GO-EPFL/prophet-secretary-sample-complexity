import ProphetSecretary.Model.CanonicalNormalization
import ProphetSecretary.Model.FiniteScalarRegularity

/-!
# Fixed-policy regret under scalar normalization

Positive homogeneity changes `R+zτ` to `λR+(1-λ)τ`. The base optimizer's
reward and duration are held fixed throughout the comparison.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.normalizedRegret_eq_durationRegret (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Ioo (0 : ℝ) 1) :
    optimalScalarValue P rho (1 - rho) -
      (P.valuePolicy hP hlam.1.le (sub_pos.mpr hlam.2).le).scalarObjective P rho (1 - rho) =
    rho * (optimalScalarValue P 1 ((1 - rho) / rho) -
      (P.valuePolicy hP zero_le_one (div_pos (sub_pos.mpr hlam.2) hlam.1).le).scalarObjective
        P 1 ((1 - rho) / rho)) := by
  have hval := optimalScalarValue_smul P hP (a := rho) (w := 1) (c := (1 - rho) / rho)
    hrho.1.le zero_le_one (div_pos (sub_pos.mpr hrho.2) hrho.1).le
  have he : rho * ((1 - rho) / rho) = 1 - rho := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hrho.1.ne']
  rw [mul_one, he] at hval
  rw [hval, RandomizedPolicy.scalarObjective_eq _ P hP, RandomizedPolicy.scalarObjective_eq _ P hP,
    P.valuePolicy_rewardNormalize_reward hP hlam.1 (sub_pos.mpr hlam.2).le,
    P.valuePolicy_rewardNormalize_duration hP hlam.1 (sub_pos.mpr hlam.2).le]
  field_simp [hrho.1.ne']

lemma Instance.scalarBregman_eq_normalizedRegret (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (rho : ℝ) :
    let C := P.valuePolicy hP hlam.1.le (sub_pos.mpr hlam.2).le
    optimalScalarValue P rho (1 - rho) - optimalScalarValue P lam (1 - lam) -
      (rho - lam) * (C.expectedReward P - C.expectedDuration P) =
      optimalScalarValue P rho (1 - rho) - C.scalarObjective P rho (1 - rho) := by
  dsimp only
  rw [← P.valuePolicy_optimal hP hlam.1 (sub_pos.mpr hlam.2).le,
    RandomizedPolicy.scalarObjective_eq _ P hP, RandomizedPolicy.scalarObjective_eq _ P hP]
  ring

lemma Instance.scalarUnit_hasDerivAt (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun rho ↦ optimalScalarValue P rho (1 - rho))
      ((P.valuePolicy hP hlam.1.le (sub_pos.mpr hlam.2).le).expectedReward P -
        (P.valuePolicy hP hlam.1.le (sub_pos.mpr hlam.2).le).expectedDuration P) lam := by
  simpa only [Instance.scalarStatePolicy, mul_one, one_mul] using P.scalarState_hasDerivAt hP hlam (u := 1) ⟨zero_le_one, le_rfl⟩

end ProphetSecretary.Model
