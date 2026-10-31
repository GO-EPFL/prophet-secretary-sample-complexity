import ProphetSecretary.Model.ScalarRegularity
import ProphetSecretary.Analysis.QuadraticSupport
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Preliminary finite scalar C^{1,1} regularity

The constants here depend explicitly on the finite number of identities. They
are uniform over all finite integrable-max laws and remaining horizons in `[0,1]`.
The universal, cardinality-independent curvature bound is a separate result.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- Differentiability is derived from the actual quadratic policy-regret bound.
The derivative is the slope of the fixed canonical base policy. -/
theorem Instance.scalarState_hasDerivAt (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    let π := P.scalarStatePolicy hP hlam hu.1
    HasDerivAt (fun rho ↦ optimalScalarValue P rho ((1 - rho) * u))
      (π.expectedReward P - u * π.expectedDuration P) lam := by
  let π := P.scalarStatePolicy hP hlam hu.1
  let a := lam / 2
  let b := (lam + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hlam.1]
  have hb : b < 1 := by dsimp [b]; linarith [hlam.2]
  have hlower : a < lam := by dsimp [a]; linarith [hlam.1]
  have hupper : lam < b := by dsimp [b]; linarith [hlam.2]
  change HasDerivAt (fun rho ↦ optimalScalarValue P rho ((1 - rho) * u))
    (π.expectedReward P - u * π.expectedDuration P) lam
  apply ProphetSecretary.Analysis.hasDerivAt_of_quadratic_remainder (K := finiteScalarConstant n a b)
  filter_upwards [Icc_mem_nhds hlower hupper] with rho hrho
  have h := P.scalarState_quadraticGap_uniform hP ha hb ⟨hlower.le, hupper.le⟩ hrho hu
  have h0 : 0 ≤ optimalScalarValue P rho ((1 - rho) * u) - optimalScalarValue P lam ((1 - lam) * u) -
      (rho - lam) * (π.expectedReward P - u * π.expectedDuration P) := h.1
  rw [abs_of_nonneg h0]
  exact h.2

lemma Instance.scalarState_differentiableOn (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    DifferentiableOn ℝ (fun lam ↦ optimalScalarValue P lam ((1 - lam) * u)) (Ioo (0 : ℝ) 1) := by
  intro lam hlam
  exact (P.scalarState_hasDerivAt hP hlam hu).differentiableAt.differentiableWithinAt

/-- Lipschitz derivative on each fixed interior scalar interval, with the
preliminary finite constant displayed explicitly. -/
theorem Instance.scalarState_deriv_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {u a b lam rho : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (ha : 0 < a) (hb : b < 1)
    (hlam : lam ∈ Icc a b) (hrho : rho ∈ Icc a b) :
    |deriv (fun z ↦ optimalScalarValue P z ((1 - z) * u)) rho -
      deriv (fun z ↦ optimalScalarValue P z ((1 - z) * u)) lam| ≤
      2 * finiteScalarConstant n a b * |rho - lam| := by
  apply ProphetSecretary.Analysis.abs_sub_slopes_le_of_quadratic (S := Icc a b)
    (f := fun z ↦ optimalScalarValue P z ((1 - z) * u))
    (g := deriv (fun z ↦ optimalScalarValue P z ((1 - z) * u)))
    (K := finiteScalarConstant n a b) ?_ hlam hrho
  intro x hx y hy
  have hx0 : x ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hderiv := (P.scalarState_hasDerivAt hP hx0 hu).deriv
  rw [hderiv]
  exact P.scalarState_quadraticGap_uniform hP ha hb hx hy hu

/-- Concrete local C^{1,1} formulation: differentiability in the interior and
an explicit Lipschitz constant for the derivative on every interior interval. -/
theorem Instance.scalarState_finite_C11 (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    DifferentiableOn ℝ (fun lam ↦ optimalScalarValue P lam ((1 - lam) * u)) (Ioo (0 : ℝ) 1) ∧
      ∀ a b : ℝ, 0 < a → b < 1 →
        ∃ L : ℝ≥0, (L : ℝ) = 2 * finiteScalarConstant n a b ∧
          LipschitzOnWith L (deriv (fun lam ↦ optimalScalarValue P lam ((1 - lam) * u))) (Icc a b) := by
  refine ⟨P.scalarState_differentiableOn hP hu, ?_⟩
  intro a b ha hb
  have hK : 0 ≤ 2 * finiteScalarConstant n a b := by
    unfold finiteScalarConstant
    positivity
  let L : ℝ≥0 := ⟨2 * finiteScalarConstant n a b, hK⟩
  refine ⟨L, rfl, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro lam hlam rho hrho
  exact P.scalarState_deriv_lipschitz hP hu ha hb hrho hlam

end ProphetSecretary.Model
