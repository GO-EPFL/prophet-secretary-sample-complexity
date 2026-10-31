import ProphetSecretary.Model.BellmanOptimal
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# State envelope identities

Paper correspondence: `eq:ps-state-envelope`. The optimal policy is fixed at
the base parameter when its affine payoff is differentiated. Differentiability
of the reoptimized value is a separate, explicit hypothesis here.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma RandomizedPolicy.hasDerivAt_stateWeightObjective (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (u lam : ℝ) :
    HasDerivAt (fun rho ↦ π.scalarObjective P rho ((1 - rho) * u))
      (π.expectedReward P - u * π.expectedDuration P) lam := by
  have heq : (fun rho ↦ π.scalarObjective P rho ((1 - rho) * u)) =
      (fun rho ↦ rho * (π.expectedReward P - u * π.expectedDuration P) + u * π.expectedDuration P) := by
    funext rho
    rw [π.scalarObjective_eq P hP]
    ring
  rw [heq]
  exact (hasDerivAt_mul_const (x := lam)
    (π.expectedReward P - u * π.expectedDuration P)).add_const (u * π.expectedDuration P)

lemma RandomizedPolicy.hasDerivAt_horizonObjective (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (w c u : ℝ) :
    HasDerivAt (fun v ↦ π.scalarObjective P w (c * v)) (c * π.expectedDuration P) u := by
  have heq : (fun v ↦ π.scalarObjective P w (c * v)) =
      (fun v ↦ v * (c * π.expectedDuration P) + w * π.expectedReward P) := by
    funext v
    rw [π.scalarObjective_eq P hP]
    ring
  rw [heq]
  exact (hasDerivAt_mul_const (x := u) (c * π.expectedDuration P)).add_const (w * π.expectedReward P)

/-- An optimizer at one scalar supplies an affine lower support at every
other admissible scalar, with that same fixed policy. -/
lemma RandomizedPolicy.stateWeight_support (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {u lam rho : ℝ} (hu : 0 ≤ u)
    (hrho : rho ∈ Icc (0 : ℝ) 1)
    (hopt : π.scalarObjective P lam ((1 - lam) * u) = optimalScalarValue P lam ((1 - lam) * u)) :
    optimalScalarValue P lam ((1 - lam) * u) +
        (rho - lam) * (π.expectedReward P - u * π.expectedDuration P) ≤
      optimalScalarValue P rho ((1 - rho) * u) := by
  have h := scalarObjective_le_optimal π P hP hrho.1 (mul_nonneg (sub_nonneg.mpr hrho.2) hu)
  rw [← hopt, π.scalarObjective_eq P hP]
  rw [π.scalarObjective_eq P hP] at h
  nlinarith

/-- At a differentiability point, the supporting payoff fixes the derivative.
This does not differentiate a parameter-dependent choice of optimizer. -/
lemma RandomizedPolicy.stateWeight_envelope (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {u lam : ℝ} (hu : 0 ≤ u)
    (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hopt : π.scalarObjective P lam ((1 - lam) * u) = optimalScalarValue P lam ((1 - lam) * u))
    (hD : DifferentiableAt ℝ (fun rho ↦ optimalScalarValue P rho ((1 - rho) * u)) lam) :
    HasDerivAt (fun rho ↦ optimalScalarValue P rho ((1 - rho) * u))
      (π.expectedReward P - u * π.expectedDuration P) lam := by
  have hmin : IsLocalMin (fun rho ↦ optimalScalarValue P rho ((1 - rho) * u) -
      π.scalarObjective P rho ((1 - rho) * u)) lam := by
    filter_upwards [Icc_mem_nhds hlam.1 hlam.2] with rho hrho
    rw [hopt, sub_self]
    exact sub_nonneg.mpr (scalarObjective_le_optimal π P hP hrho.1 (mul_nonneg (sub_nonneg.mpr hrho.2) hu))
  have hz := hmin.hasDerivAt_eq_zero (hD.hasDerivAt.sub (π.hasDerivAt_stateWeightObjective P hP u lam))
  have he : deriv (fun rho ↦ optimalScalarValue P rho ((1 - rho) * u)) lam =
      π.expectedReward P - u * π.expectedDuration P := sub_eq_zero.mp hz
  simpa only [he] using hD.hasDerivAt

lemma RandomizedPolicy.horizon_envelope (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hu : 0 < u) (hopt : π.scalarObjective P w (c * u) = optimalScalarValue P w (c * u))
    (hD : DifferentiableAt ℝ (fun v ↦ optimalScalarValue P w (c * v)) u) :
    HasDerivAt (fun v ↦ optimalScalarValue P w (c * v)) (c * π.expectedDuration P) u := by
  have hmin : IsLocalMin (fun v ↦ optimalScalarValue P w (c * v) - π.scalarObjective P w (c * v)) u := by
    filter_upwards [Ici_mem_nhds hu] with v hv
    rw [hopt, sub_self]
    exact sub_nonneg.mpr (scalarObjective_le_optimal π P hP hw (mul_nonneg hc hv))
  have hz := hmin.hasDerivAt_eq_zero (hD.hasDerivAt.sub (π.hasDerivAt_horizonObjective P hP w c u))
  have he : deriv (fun v ↦ optimalScalarValue P w (c * v)) u = c * π.expectedDuration P := sub_eq_zero.mp hz
  simpa only [he] using hD.hasDerivAt

/-- The canonical optimizer at normalized weight `lam` and remaining horizon
`u`; its duration is still normalized to a unit clock interval. -/
noncomputable def Instance.scalarStatePolicy (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) : RandomizedPolicy n :=
  P.valuePolicy hP hlam.1.le (mul_nonneg (sub_nonneg.mpr hlam.2.le) hu)

/-- The value identity in `eq:ps-state-envelope`, with accrued duration excluded. -/
theorem Instance.scalarState_value (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) :
    let π := P.scalarStatePolicy hP hlam hu
    optimalScalarValue P lam ((1 - lam) * u) =
      lam * π.expectedReward P + ((1 - lam) * u) * π.expectedDuration P := by
  let π := P.scalarStatePolicy hP hlam hu
  have hopt := P.valuePolicy_optimal hP hlam.1 (mul_nonneg (sub_nonneg.mpr hlam.2.le) hu)
  exact hopt.symm.trans (π.scalarObjective_eq P hP lam ((1 - lam) * u))

/-- The normalized-weight envelope formula for an actual canonical base optimizer. -/
theorem Instance.scalarState_weight_envelope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u)
    (hD : DifferentiableAt ℝ (fun rho ↦ optimalScalarValue P rho ((1 - rho) * u)) lam) :
    let π := P.scalarStatePolicy hP hlam hu
    HasDerivAt (fun rho ↦ optimalScalarValue P rho ((1 - rho) * u))
      (π.expectedReward P - u * π.expectedDuration P) lam := by
  exact (P.scalarStatePolicy hP hlam hu).stateWeight_envelope P hP hu hlam
    (P.valuePolicy_optimal hP hlam.1 (mul_nonneg (sub_nonneg.mpr hlam.2.le) hu)) hD

/-- The remaining-horizon envelope formula for an actual canonical base policy.
`u` is remaining time, so the derivative sign is nonnegative. -/
theorem Instance.remainingHorizon_envelope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u)
    (hD : DifferentiableAt ℝ (fun v ↦ optimalScalarValue P w (c * v)) u) :
    let π := P.valuePolicy hP hw.le (mul_nonneg hc hu.le)
    HasDerivAt (fun v ↦ optimalScalarValue P w (c * v)) (c * π.expectedDuration P) u := by
  exact (P.valuePolicy hP hw.le (mul_nonneg hc hu.le)).horizon_envelope P hP hw.le hc hu
    (P.valuePolicy_optimal hP hw (mul_nonneg hc hu.le)) hD

end ProphetSecretary.Model
