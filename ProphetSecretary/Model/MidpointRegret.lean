import ProphetSecretary.Model.BellmanOptimal
import ProphetSecretary.Reach.Robust

/-!
# Endpoint regrets of a midpoint optimizer

The fixed-policy objective and benchmark are affine in the scalar weight.
Midpoint optimality therefore identifies the sum of endpoint regrets exactly,
and the proved global scalar inequality bounds each by the two endpoint gaps.
This is `updual:endpointregret`, for all general policies optimal at the midpoint.
-/
open MeasureTheory Set
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def RandomizedPolicy.normalizedRegret (π : RandomizedPolicy n) (P : Instance n) (lam : ℝ) : ℝ :=
  optimalScalarValue P lam (1 - lam) - π.scalarObjective P lam (1 - lam)

lemma RandomizedPolicy.normalizedRegret_nonnegative (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1) :
    0 ≤ π.normalizedRegret P lam :=
  sub_nonneg.mpr (scalarObjective_le_optimal π P hP hlam.1 (sub_nonneg.mpr hlam.2))

/-- Exact identity in `updual:endpointregret`, without selecting a new
optimizer at either endpoint. -/
lemma RandomizedPolicy.midpoint_endpointRegret_sum (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (lam₁ lam₂ : ℝ)
    (hopt : π.scalarObjective P ((lam₁ + lam₂) / 2) (1 - (lam₁ + lam₂) / 2) =
      optimalScalarValue P ((lam₁ + lam₂) / 2) (1 - (lam₁ + lam₂) / 2)) :
    π.normalizedRegret P lam₁ + π.normalizedRegret P lam₂ =
      normalizedScalarGap P lam₁ + normalizedScalarGap P lam₂ -
        2 * normalizedScalarGap P ((lam₁ + lam₂) / 2) := by
  rw [π.scalarObjective_eq P hP] at hopt
  unfold normalizedRegret normalizedScalarGap scalarGap
  rw [π.scalarObjective_eq P hP, π.scalarObjective_eq P hP]
  nlinarith only [hopt]

theorem RandomizedPolicy.midpoint_endpointRegrets (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam₁ lam₂ : ℝ}
    (hlam₁ : lam₁ ∈ Icc (0 : ℝ) 1) (hlam₂ : lam₂ ∈ Icc (0 : ℝ) 1)
    (hopt : π.scalarObjective P ((lam₁ + lam₂) / 2) (1 - (lam₁ + lam₂) / 2) =
      optimalScalarValue P ((lam₁ + lam₂) / 2) (1 - (lam₁ + lam₂) / 2)) :
    0 ≤ π.normalizedRegret P lam₁ ∧ 0 ≤ π.normalizedRegret P lam₂ ∧
      π.normalizedRegret P lam₁ ≤ normalizedScalarGap P lam₁ + normalizedScalarGap P lam₂ ∧
      π.normalizedRegret P lam₂ ≤ normalizedScalarGap P lam₁ + normalizedScalarGap P lam₂ := by
  have hr₁ := π.normalizedRegret_nonnegative P hP hlam₁
  have hr₂ := π.normalizedRegret_nonnegative P hP hlam₂
  have hmid : (lam₁ + lam₂) / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hlam₁.1,hlam₁.2,hlam₂.1,hlam₂.2]
  have hg := normalizedScalarGap_nonnegative P hP hmid
  have heq := π.midpoint_endpointRegret_sum P hP lam₁ lam₂ hopt
  exact ⟨hr₁,hr₂,by linarith only [hr₂,hg,heq],by linarith only [hr₁,hg,heq]⟩

/-- Actual canonical-midpoint specialization of `updual:endpointregret`.
Its optimality against every admissible policy is the proved Bellman theorem. -/
theorem Instance.canonical_midpoint_endpointRegrets (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam₁ lam₂ : ℝ}
    (hlam₁ : lam₁ ∈ Ioo (0 : ℝ) 1) (hlam₂ : lam₂ ∈ Ioo (0 : ℝ) 1) :
    let hw : 0 < (lam₁ + lam₂) / 2 := by linarith [hlam₁.1,hlam₂.1]
    let hc : 0 ≤ 1 - (lam₁ + lam₂) / 2 := by linarith [hlam₁.2,hlam₂.2]
    let π := P.valuePolicy hP hw.le hc
    0 ≤ π.normalizedRegret P lam₁ ∧ 0 ≤ π.normalizedRegret P lam₂ ∧
      π.normalizedRegret P lam₁ ≤ normalizedScalarGap P lam₁ + normalizedScalarGap P lam₂ ∧
      π.normalizedRegret P lam₂ ≤ normalizedScalarGap P lam₁ + normalizedScalarGap P lam₂ := by
  dsimp only
  apply RandomizedPolicy.midpoint_endpointRegrets _ P hP ⟨hlam₁.1.le,hlam₁.2.le⟩ ⟨hlam₂.1.le,hlam₂.2.le⟩
  exact P.valuePolicy_optimal hP (by linarith [hlam₁.1,hlam₂.1]) (by linarith [hlam₁.2,hlam₂.2])

end ProphetSecretary.Model
