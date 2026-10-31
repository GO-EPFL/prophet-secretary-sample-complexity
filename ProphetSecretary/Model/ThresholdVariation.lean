import ProphetSecretary.Model.ScalarSupport
import ProphetSecretary.Model.BellmanPathLoss
import ProphetSecretary.Analysis.ThresholdLoss
import Mathlib.Tactic.FieldSimp

/-!
# Variation of normalized scalar thresholds

Reward normalization rewrites `V(P;w,c)/w` as `V(P;1,c/w)`. The latter is
one-Lipschitz in duration's coefficient. Consequently threshold errors scale
with the remaining horizon, rather than with the offer cap or instance size.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.optimalScalarValue_div_reward (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue P w c / w = optimalScalarValue P 1 (c / w) := by
  have h := optimalScalarValue_smul P hP (a := w) (w := 1) (c := c / w) hw.le zero_le_one
    (div_nonneg hc hw.le)
  have he : w * (c / w) = c := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hw.ne']
  rw [mul_one, he] at h
  rw [h, mul_div_cancel_left₀ _ hw.ne']

lemma Instance.valueThreshold_rewardNormalize (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (A : Finset (Fin n)) (t : ℝ) (i : Fin n) :
    P.valueThreshold w c A t i =
      optimalScalarValue (P.restrictTo (A.erase i)) 1 ((c * max 0 (1 - t)) / w) := by
  exact (P.restrictTo (A.erase i)).optimalScalarValue_div_reward
    (P.restrictTo_integrable_maximum _ hP) hw (mul_nonneg hc (le_max_left _ _))

/-- Exact remaining-time dependence of threshold variation. No offer cap or
cardinality factor is present. -/
theorem Instance.stateThreshold_weight_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u)
    (A : Finset (Fin n)) (t : ℝ) (i : Fin n) :
    |P.valueThreshold lam ((1 - lam) * u) A t i - P.valueThreshold rho ((1 - rho) * u) A t i| ≤
      u * max 0 (1 - t) * |lam - rho| / (lam * rho) := by
  have hcL := mul_nonneg (sub_nonneg.mpr hlam.2.le) hu
  have hcR := mul_nonneg (sub_nonneg.mpr hrho.2.le) hu
  rw [P.valueThreshold_rewardNormalize hP hlam.1 hcL, P.valueThreshold_rewardNormalize hP hrho.1 hcR]
  let Q := P.restrictTo (A.erase i)
  have h := optimalScalarValue_durationWeight_lipschitz Q (P.restrictTo_integrable_maximum _ hP) zero_le_one
    (div_nonneg (mul_nonneg hcL (le_max_left 0 (1 - t))) hlam.1.le)
    (div_nonneg (mul_nonneg hcR (le_max_left 0 (1 - t))) hrho.1.le)
  have he : (((1 - lam) * u) * max 0 (1 - t)) / lam - (((1 - rho) * u) * max 0 (1 - t)) / rho =
      (u * max 0 (1 - t)) * (rho - lam) / (lam * rho) := by
    field_simp [hlam.1.ne', hrho.1.ne']
    ring
  rw [he, abs_div, abs_mul, abs_of_nonneg (mul_nonneg hu (le_max_left _ _)),
    abs_sub_comm rho lam, abs_of_pos (mul_pos hlam.1 hrho.1)] at h
  exact h

lemma Instance.stateThreshold_weight_lipschitz_elapsed (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u)
    (A : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) (i : Fin n) :
    |P.valueThreshold lam ((1 - lam) * u) A t i - P.valueThreshold rho ((1 - rho) * u) A t i| ≤
      u * |lam - rho| / (lam * rho) := by
  have h := P.stateThreshold_weight_lipschitz hP hlam hrho hu A t i
  have hmax : max 0 (1 - t) ≤ 1 := max_le zero_le_one (sub_le_self 1 ht)
  have hp : u * max 0 (1 - t) * |lam - rho| ≤ u * |lam - rho| := by
    calc
      _ = (u * |lam - rho|) * max 0 (1 - t) := by ring
      _ ≤ (u * |lam - rho|) * 1 := mul_le_mul_of_nonneg_left hmax (mul_nonneg hu (abs_nonneg _))
      _ = _ := mul_one _
  exact h.trans (div_le_div_of_nonneg_right hp (mul_pos hlam.1 hrho.1).le)

/-- Bellman-payoff scale uses the new reward coefficient `rho`. -/
lemma Instance.stateThreshold_scaled_shift (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u)
    (A : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) (i : Fin n) :
    |rho * P.valueThreshold lam ((1 - lam) * u) A t i -
      rho * P.valueThreshold rho ((1 - rho) * u) A t i| ≤ u * |lam - rho| / lam := by
  rw [← mul_sub, abs_mul, abs_of_pos hrho.1]
  calc
    _ ≤ rho * (u * |lam - rho| / (lam * rho)) :=
      mul_le_mul_of_nonneg_left (P.stateThreshold_weight_lipschitz_elapsed hP hlam hrho hu A ht i) hrho.1.le
    _ = _ := by field_simp [hlam.1.ne', hrho.1.ne']

/-- The old optimizer's action loss under the new weight is bounded by its
remaining-horizon threshold error and supported on the corresponding true band. -/
theorem Instance.oldPolicy_localLoss_le_band (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u)
    (x a : Fin n → ℝ) (i : Fin n) (ht : 0 ≤ a i) :
    (thresholdPolicy (fun (_ : Unit) A t j ↦ P.valueThreshold lam ((1 - lam) * u) A t j)).arrivalBellmanLoss
      P rho ((1 - rho) * u) () x a i ≤
      if |rho * x i - P.continuationAtArrival rho ((1 - rho) * u) x a i| ≤ u * |lam - rho| / lam then
        u * |lam - rho| / lam else 0 := by
  let A := unseen (history Finset.univ x a (a i))
  let old := P.valueThreshold lam ((1 - lam) * u) A (a i) i
  let new := P.valueThreshold rho ((1 - rho) * u) A (a i) i
  let π : Policy Unit n := thresholdPolicy (fun (_ : Unit) B t j ↦ P.valueThreshold lam ((1 - lam) * u) B t j)
  have hV : P.continuationAtArrival rho ((1 - rho) * u) x a i = rho * new :=
    P.continuationAtArrival_eq_threshold hrho.1 _ x a i
  have ha : (π.action () Finset.univ x a i = true) ↔ rho * old ≤ rho * x i := by
    change Decidable.decide (old ≤ x i) = true ↔ _
    rw [decide_eq_true_eq, mul_le_mul_iff_right₀ hrho.1]
  have hshift := P.stateThreshold_scaled_shift hP hlam hrho hu A ht i
  have h := ProphetSecretary.Analysis.max_action_loss_le_band (a := rho * x i) (old := rho * old) (b := rho * new) hshift
  change π.arrivalBellmanLoss P rho ((1 - rho) * u) () x a i ≤ _
  unfold Policy.arrivalBellmanLoss
  rw [hV]
  simpa only [ha] using h

end ProphetSecretary.Model
