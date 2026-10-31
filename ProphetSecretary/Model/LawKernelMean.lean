import ProphetSecretary.Model.LawKernelCharge
import ProphetSecretary.Reach.TailLifting

/-! # Expected directional adaptation charge
All unseen states are charged before averaging each candidate value. The
result involves the sum of actual marginal first moments and has no dependence
on the number of variables.
-/
open MeasureTheory Set
open scoped BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

theorem Instance.mean_lawAdaptationKernel_le (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    let Q := P.likelihoodWidePath h hh hb hm θ
    (∑ i : Fin n, ∫ ω : World n Unit,
      (∑ A : Finset (Fin n), P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω) / 2
      ∂Q.worldLaw (Measure.dirac ())) ≤
        2 * w ^ 2 * H * information P.law h / c * Q.totalFirstMoment := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQB := P.likelihoodWidePath_bounded h hh hb hm θ hbound
  have hQ := Q.integrable_maximum_of_bounded hQB
  let K := 2 * w ^ 2 * H * information P.law h / c
  have hEach (i : Fin n) : (∫ ω : World n Unit,
      (∑ A : Finset (Fin n), P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω) / 2
      ∂Q.worldLaw (Measure.dirac ())) ≤ K * ∫ a, a ∂Q.law i := by
    have hp := Q.world_value_measurePreserving (Measure.dirac ()) i
    have hXi := hp.integrable_comp_of_integrable (Q.integrable_maximum_iff.mp hQ i)
    have hMean : (∫ ω : World n Unit, ω.1 i ∂Q.worldLaw (Measure.dirac ())) = ∫ a, a ∂Q.law i := by
      have he := integral_map (μ := Q.worldLaw (Measure.dirac ())) hp.measurable.aemeasurable aestronglyMeasurable_id
      rw [hp.map_eq] at he
      exact he.symm
    calc
      _ ≤ ∫ ω : World n Unit, K * ω.1 i ∂Q.worldLaw (Measure.dirac ()) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun ω ↦ div_nonneg
            (Finset.sum_nonneg (fun A _ ↦ P.lawAdaptationKernel_nonnegative hw hc hbound h hh hb hm θ i A ω)) (by norm_num)))
          (hXi.const_mul K)
        filter_upwards [Q.world_values_mem_Icc_ae (Measure.dirac ()) hQB] with ω hω
        have hB := div_le_div_of_nonneg_right
          (P.sum_lawAdaptationKernel_le hw hc hH hbound h hh hb hm hθ i ω (hω i).1) (by norm_num : (0 : ℝ) ≤ 2)
        convert hB using 1
        dsimp only [K, Function.comp_apply, id_eq]
        ring
      _ = _ := by rw [integral_const_mul, hMean]
  change _ ≤ K * Q.totalFirstMoment
  calc
    _ ≤ ∑ i : Fin n, K * ∫ a, a ∂Q.law i := Finset.sum_le_sum (fun i _ ↦ hEach i)
    _ = _ := by rw [← Finset.mul_sum]; rfl

end ProphetSecretary.Model
