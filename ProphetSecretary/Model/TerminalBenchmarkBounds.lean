import ProphetSecretary.Model.TerminalBenchmark
import ProphetSecretary.Model.TerminalScalarValue
import ProphetSecretary.Model.TerminalZeroWeight

/-!
# Bounded auxiliary terminal benchmarks and cap terminal values

These include zero-mean and empty instances. At a terminal reward equal to the
common cap, waiting attains the exact scalar value wH+c.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.integrable_terminalMaximum (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun x => max a (Instance.maximum x)) P.valuesLaw := by
  apply ((integrable_const a).add hP).mono'
    (measurable_const.max Instance.measurable_maximum).aestronglyMeasurable
  filter_upwards [] with x
  have hx := Instance.maximum_nonnegative x
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_of_le_right hx)]
  exact max_le (le_add_of_nonneg_right hx) (le_add_of_nonneg_left ha)

lemma Instance.terminal_benchmark_comparison (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ P.expectedTerminalMaximum a-P.expectedMaximum ∧
      P.expectedTerminalMaximum a-P.expectedMaximum ≤ a := by
  have hMax := P.integrable_terminalMaximum hP ha
  have hLower := integral_mono hP hMax (fun x => le_max_right a (Instance.maximum x))
  have hUpper := integral_mono hMax (hP.add (integrable_const a)) (fun x => by
    change max a (Instance.maximum x) ≤ Instance.maximum x+a
    have hx := Instance.maximum_nonnegative x
    exact max_le (le_add_of_nonneg_left hx) (le_add_of_nonneg_right ha))
  change P.expectedTerminalMaximum a ≤ ∫ x, Instance.maximum x+a ∂P.valuesLaw at hUpper
  rw [integral_add hP (integrable_const a),integral_const] at hUpper
  simp only [probReal_univ,one_smul] at hUpper
  constructor
  · exact sub_nonneg.mpr hLower
  · change P.expectedTerminalMaximum a ≤ P.expectedMaximum+a at hUpper
    linarith only [hUpper]

lemma Instance.expectedTerminalMaximum_at_cap (P : Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) : P.expectedTerminalMaximum H = (H : ℝ) := by
  have hx : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ (H : ℝ) :=
    ae_all_iff.mpr (fun i => (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hcap i))
  have he : (fun x => max (H : ℝ) (Instance.maximum x)) =ᵐ[P.valuesLaw] fun _ => (H : ℝ) :=
    hx.mono (fun x hx => max_eq_left (Instance.maximum_le x H.property hx))
  unfold Instance.expectedTerminalMaximum
  rw [integral_congr_ae he,integral_const]
  simp only [probReal_univ,one_smul]

lemma Instance.optimalTerminalScalarValue_at_cap (P : Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalTerminalScalarValue P H w c = w*(H : ℝ)+c := by
  by_cases hw0 : w = 0
  · subst w
    rw [optimalTerminalScalarValue_zero_rewardWeight _ _ hc]
    simp only [zero_mul,zero_add]
  have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hP := P.integrable_maximum_of_bounded hcap
  have hQ := P.excessOffers_integrable_maximum hP H.property
  have hM := P.expectedTerminalMaximum_eq_excess hP H.property
  have he : (H : ℝ) = (H : ℝ)+(P.excessOffers H).expectedMaximum :=
    (P.expectedTerminalMaximum_at_cap H hcap).symm.trans hM
  have hM0 : (P.excessOffers H).expectedMaximum = 0 := by linarith only [he]
  have hUpper := optimalScalarValue_le_benchmark (P.excessOffers H) hQ hw hc
  rw [hM0,mul_zero,zero_add] at hUpper
  have hLower := durationWeight_le_optimalScalarValue (P.excessOffers H) hQ hw hc
  exact (optimalTerminalScalarValue_eq_excessValue P hP H.property hwP hc).trans
    (congrArg (fun z : ℝ => w*(H : ℝ)+z) (le_antisymm hUpper hLower))

end ProphetSecretary.Model
