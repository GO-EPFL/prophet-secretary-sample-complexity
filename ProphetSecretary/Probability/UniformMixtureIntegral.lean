import ProphetSecretary.Model.DurationLower
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Affine expectations from one independent uniform mixture coin

The coin is drawn once and chooses one complete online execution. Its
independence from the execution world gives the convex combination of
expectations, including when the mixing weight was fixed by earlier data.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

lemma integral_uniform_coin_ite {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) (a b : ℝ) :
    (∫ c, if c<α then b else a ∂Model.Instance.uniformClock)=(1-α)*a+α*b := by
  let E : Set ℝ := Iio α
  have hE : MeasurableSet E := measurableSet_Iio
  have he : (fun c : ℝ => if c<α then b else a) =
      fun c => E.indicator (fun _ => b) c+Eᶜ.indicator (fun _ => a) c := by
    funext c
    by_cases hc : c<α
    · simp [E,hc,not_le_of_gt hc]
    · simp [E,hc,le_of_not_gt hc]
  rw [he, integral_add (f := E.indicator (fun _ => b)) (g := Eᶜ.indicator (fun _ => a))
      ((integrable_const b).indicator hE) ((integrable_const a).indicator hE.compl),
    integral_indicator_const b hE, integral_indicator_const a hE.compl,
    smul_eq_mul, smul_eq_mul, measureReal_compl hE, probReal_univ]
  rw [Model.Instance.uniformClock_probability_lt hα.1 hα.2]
  ring

lemma integrable_uniform_coin_choice {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (α : ℝ) :
    Integrable (fun p : Ω × ℝ => if p.2<α then g p.1 else f p.1) (μ.prod Model.Instance.uniformClock) := by
  have hF : Integrable (fun p : Ω × ℝ => f p.1) (μ.prod Model.Instance.uniformClock) :=
    measurePreserving_fst.integrable_comp_of_integrable hf
  have hG : Integrable (fun p : Ω × ℝ => g p.1) (μ.prod Model.Instance.uniformClock) :=
    measurePreserving_fst.integrable_comp_of_integrable hg
  have hE : MeasurableSet {p : Ω × ℝ | p.2<α} := measurableSet_lt measurable_snd measurable_const
  exact Integrable.piecewise hE hG.integrableOn hF.integrableOn

lemma integral_uniform_coin_choice {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    (∫ p : Ω × ℝ, if p.2<α then g p.1 else f p.1 ∂μ.prod Model.Instance.uniformClock) =
      (1-α)*(∫ ω, f ω ∂μ)+α*(∫ ω, g ω ∂μ) := by
  rw [integral_prod _ (integrable_uniform_coin_choice μ hf hg α)]
  simp_rw [integral_uniform_coin_ite hα]
  rw [integral_add (f := fun ω => (1-α)*f ω) (g := fun ω => α*g ω)
    (hf.const_mul _) (hg.const_mul _), integral_const_mul, integral_const_mul]

end ProphetSecretary.Probability
