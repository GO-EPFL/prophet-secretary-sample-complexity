import ProphetSecretary.Limiting.PoissonBenchmarkComparison
import ProphetSecretary.Model.TerminalBenchmark

/-!
# Dense finite offers and the auxiliary terminal maximum

The no-large-offer probability is an actual product void probability. This
benchmark comparison is separate from the online fallback-policy argument.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma finite_maximum_cdf_le_exp (P : Model.Instance n) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    P.valuesLaw.real {x | Model.Instance.maximum x ≤ ℓ} ≤ Real.exp (-P.tailCount ℓ) := by
  rw [finite_maximum_real_Iic P hℓ]
  have h := ProphetSecretary.Analysis.bernoulli_void_comparison (fun i => (P.law i).real (Ioi ℓ))
    (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
  have hc (i : Fin n) : (P.law i).real (Iic ℓ) = 1-(P.law i).real (Ioi ℓ) := by
    rw [show Iic ℓ = (Ioi ℓ)ᶜ by ext x; simp,measureReal_compl measurableSet_Ioi,probReal_univ]
  simp only [hc]
  change (∏ i : Fin n, (1-(P.law i).real (Ioi ℓ))) ≤ Real.exp (-(∑ i : Fin n, (P.law i).real (Ioi ℓ)))
  linarith only [h.1]

theorem dense_terminal_benchmark_comparison (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {ℓ b H : ℝ}
    (hℓ : 0 ≤ ℓ) (hℓb : ℓ ≤ b) (hbH : b ≤ H) :
    0 ≤ P.expectedTerminalMaximum b-P.expectedMaximum ∧
      P.expectedTerminalMaximum b-P.expectedMaximum ≤ b-ℓ+H*Real.exp (-P.tailCount ℓ) := by
  let E : Set (Fin n → ℝ) := {x | Model.Instance.maximum x ≤ ℓ}
  let J : (Fin n → ℝ) → ℝ := fun x => if x ∈ E then 1 else 0
  have hE : MeasurableSet E := measurableSet_le Model.Instance.measurable_maximum measurable_const
  have hJI : Integrable J P.valuesLaw := by
    apply Integrable.of_bound (Measurable.ite hE measurable_const measurable_const).aestronglyMeasurable 1
    filter_upwards [] with x
    dsimp [J]
    split_ifs <;> norm_num
  have hJE : (∫ x, J x ∂P.valuesLaw) = P.valuesLaw.real E := by
    simpa only [J,Set.indicator_apply,Pi.one_apply] using integral_indicator_one (μ := P.valuesLaw) hE
  have hb : 0 ≤ b := hℓ.trans hℓb
  have hMax : Integrable (fun x => max b (Model.Instance.maximum x)) P.valuesLaw := by
    apply ((integrable_const b).add hP).mono'
      (measurable_const.max Model.Instance.measurable_maximum).aestronglyMeasurable
    filter_upwards [] with x
    have hx := Model.Instance.maximum_nonnegative x
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_of_le_right hx)]
    exact max_le (le_add_of_nonneg_right hx) (le_add_of_nonneg_left hb)
  have hLower := integral_mono hP hMax (fun x => le_max_right b (Model.Instance.maximum x))
  have hUpper := integral_mono hMax ((hP.add (integrable_const (b-ℓ))).add (hJI.const_mul H)) (fun x => by
    have hx0 := Model.Instance.maximum_nonnegative x
    change max b (Model.Instance.maximum x) ≤ Model.Instance.maximum x+(b-ℓ)+H*J x
    by_cases hx : Model.Instance.maximum x ≤ ℓ
    · have hxb := hx.trans hℓb
      rw [max_eq_left hxb]
      change b ≤ Model.Instance.maximum x+(b-ℓ)+H*(if x ∈ E then 1 else 0)
      rw [if_pos (show x ∈ E from hx),mul_one]
      linarith only [hx0,hℓb,hbH]
    · change max b (Model.Instance.maximum x) ≤ Model.Instance.maximum x+(b-ℓ)+H*(if x ∈ E then 1 else 0)
      rw [if_neg (show x ∉ E from hx),mul_zero,add_zero]
      apply max_le
      · linarith only [hx]
      · linarith only [hℓb])
  change P.expectedTerminalMaximum b ≤ ∫ x, Model.Instance.maximum x+(b-ℓ)+H*J x ∂P.valuesLaw at hUpper
  rw [integral_add (f := fun x => Model.Instance.maximum x+(b-ℓ)) (g := fun x => H*J x)
    (hP.add (integrable_const (b-ℓ))) (hJI.const_mul H),integral_add hP (integrable_const (b-ℓ)),
    integral_const,integral_const_mul,hJE] at hUpper
  simp only [probReal_univ,one_smul] at hUpper
  have hVoid := finite_maximum_cdf_le_exp P hℓ
  have hBound := mul_le_mul_of_nonneg_left hVoid (hℓ.trans (hℓb.trans hbH))
  constructor
  · exact sub_nonneg.mpr hLower
  · change H*P.valuesLaw.real E ≤ _ at hBound
    change P.expectedTerminalMaximum b ≤ P.expectedMaximum+(b-ℓ)+H*P.valuesLaw.real E at hUpper
    linarith only [hUpper,hBound]

end ProphetSecretary.Limiting
