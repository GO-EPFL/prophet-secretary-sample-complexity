import ProphetSecretary.Model.ScalarEnvelope
import ProphetSecretary.Model.DurationLower

/-!
# Quantitative scalar support and finite time separation

The base optimizer is held fixed when duration's coefficient changes. Its actual
cardinality lower bound yields strong growth in remaining time. This argument
also applies at zero remaining coefficient and never sets `V(P;w,0)` to zero.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma RandomizedPolicy.horizon_support (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u v : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hopt : π.scalarObjective P w (c * v) = optimalScalarValue P w (c * v)) :
    optimalScalarValue P w (c * v) + c * (u - v) * π.expectedDuration P ≤
      optimalScalarValue P w (c * u) := by
  have h := scalarObjective_le_optimal π P hP hw (mul_nonneg hc hu)
  rw [← hopt, π.scalarObjective_eq P hP]
  rw [π.scalarObjective_eq P hP] at h
  nlinarith

lemma Instance.remainingHorizon_support (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u v : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    let π := P.valuePolicy hP hw.le (mul_nonneg hc hv)
    optimalScalarValue P w (c * v) + c * (u - v) * π.expectedDuration P ≤
      optimalScalarValue P w (c * u) := by
  exact (P.valuePolicy hP hw.le (mul_nonneg hc hv)).horizon_support P hP hw.le hc hu
    (P.valuePolicy_optimal hP hw (mul_nonneg hc hv))

/-- Strong increase in remaining horizon, with an explicit finite cardinality
constant obtained from an actual canonical policy's duration. -/
theorem Instance.remainingHorizon_growth (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u v : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hv : 0 ≤ v) (hvu : v ≤ u) :
    (c / (4 * (1 + (n : ℝ)))) * (u - v) ≤
      optimalScalarValue P w (c * u) - optimalScalarValue P w (c * v) := by
  let π := P.valuePolicy hP hw.le (mul_nonneg hc hv)
  have hT := π.expectedDuration_ge_card_bound P
  have hs := P.remainingHorizon_support hP hw hc (hv.trans hvu) hv
  calc
    _ = (c * (u - v)) * (1 / (4 * (1 + (n : ℝ)))) := by ring
    _ ≤ (c * (u - v)) * π.expectedDuration P :=
      mul_le_mul_of_nonneg_left hT (mul_nonneg hc (sub_nonneg.mpr hvu))
    _ ≤ _ := by linarith

/-- The same strong-growth constant may use the original instance size for
every child subset; no child is silently treated as having zero initial value. -/
theorem Instance.continuationValue_growth (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (A : Finset (Fin n))
    {w c u v : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (hv : 0 ≤ v) (hvu : v ≤ u) :
    (c / (4 * (1 + (n : ℝ)))) * (u - v) ≤
      P.continuationValue A u w c - P.continuationValue A v w c := by
  have hcard : (A.card : ℝ) ≤ n := by exact_mod_cast (A.card_le_univ.trans_eq (Fintype.card_fin n))
  have hden : 4 * (1 + (A.card : ℝ)) ≤ 4 * (1 + (n : ℝ)) := by linarith
  have hrate : c / (4 * (1 + (n : ℝ))) ≤ c / (4 * (1 + (A.card : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hden) hc
    simpa only [div_eq_mul_inv, one_div, one_mul] using h
  exact (mul_le_mul_of_nonneg_right hrate (sub_nonneg.mpr hvu)).trans
    ((P.restrictTo A).remainingHorizon_growth (P.restrictTo_integrable_maximum A hP) hw hc hv hvu)

/-- Uniform normalized-weight continuity at a fixed remaining horizon. -/
theorem Instance.stateWeight_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {u lam rho : ℝ}
    (hu : 0 ≤ u) (hlam : lam ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 1) :
    |optimalScalarValue P lam ((1 - lam) * u) - optimalScalarValue P rho ((1 - rho) * u)| ≤
      (P.expectedMaximum + u) * |lam - rho| := by
  have h := optimalScalarValue_coefficients_lipschitz P hP hlam.1
    (mul_nonneg (sub_nonneg.mpr hlam.2) hu) hrho.1 (mul_nonneg (sub_nonneg.mpr hrho.2) hu)
  have he : (1 - lam) * u - (1 - rho) * u = -((lam - rho) * u) := by ring
  rw [he, abs_neg, abs_mul, abs_of_nonneg hu] at h
  calc
    _ ≤ P.expectedMaximum * |lam - rho| + |lam - rho| * u := h
    _ = _ := by ring

/-- The acceptance gap changes linearly with the scalar parameter, with every
constant and dependence displayed before a band argument is applied. -/
theorem Instance.stateGap_weight_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {u lam rho x : ℝ}
    (hu : 0 ≤ u) (hlam : lam ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    |(lam * x - optimalScalarValue P lam ((1 - lam) * u)) -
      (rho * x - optimalScalarValue P rho ((1 - rho) * u))| ≤
      (x + P.expectedMaximum + u) * |lam - rho| := by
  have he : (lam * x - optimalScalarValue P lam ((1 - lam) * u)) -
      (rho * x - optimalScalarValue P rho ((1 - rho) * u)) =
      (lam - rho) * x - (optimalScalarValue P lam ((1 - lam) * u) - optimalScalarValue P rho ((1 - rho) * u)) := by ring
  rw [he]
  calc
    _ ≤ |(lam - rho) * x| + |optimalScalarValue P lam ((1 - lam) * u) - optimalScalarValue P rho ((1 - rho) * u)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le ((lam - rho) * x) 0 _)
    _ ≤ |lam - rho| * x + (P.expectedMaximum + u) * |lam - rho| := by
      rw [abs_mul, abs_of_nonneg hx]
      exact add_le_add le_rfl (P.stateWeight_lipschitz hP hu hlam hrho)
    _ = _ := by ring

end ProphetSecretary.Model
