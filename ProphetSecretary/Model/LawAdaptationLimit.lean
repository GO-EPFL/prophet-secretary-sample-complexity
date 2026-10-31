import ProphetSecretary.Model.LawKernelExpectation

/-! # The finite optimized-minus-frozen law adaptation limit
The optimizer in the subtracted payoff is fixed at the base law. Bellman's
performance identity and candidate-clock disintegration identify its entire
adaptation regret with the conditional losses averaged above.
-/
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma Instance.lawAdaptationRegret_eq_sum_conditional (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) :
    let Q := P.likelihoodWidePath h hh hb hm θ
    let T := P.likelihoodWidePath h hh hb hm ρ
    let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
    optimalScalarValue T w c - (Q.valuePolicy hQ hw.le hc).scalarObjective T w c =
      ∑ i : Fin n, ∫ ω : World n Unit, P.lawConditionalRegret hw hc hbound h hh hb hm θ ρ i ω
        ∂T.worldLaw (Measure.dirac ()) := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  have hT := T.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm ρ hbound)
  let C := Q.valuePolicy hQ hw.le hc
  change optimalScalarValue T w c - C.scalarObjective T w c = _
  rw [C.bellman_performanceDifference T hT hw hc]
  exact C.rule.integral_reachedBellmanLoss_eq_sum_clockConditional C.measurable_rule T T hT hT C.seedLaw hw hc

theorem Instance.lawAdaptationRegret_kernel_limit_ae (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-(1 / 4) : ℝ) (1 / 4)),
      let Q := P.likelihoodWidePath h hh hb hm θ
      let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
      let C := Q.valuePolicy hQ hw.le hc.le
      Tendsto (fun δ : ℝ ↦ (optimalScalarValue (P.likelihoodWidePath h hh hb hm (θ + δ)) w c -
        C.scalarObjective (P.likelihoodWidePath h hh hb hm (θ + δ)) w c) / δ ^ 2)
        (𝓝[≠] 0) (𝓝 (∑ i : Fin n, ∫ ω : World n Unit,
          (∑ A : Finset (Fin n), P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω) / 2
          ∂Q.worldLaw (Measure.dirac ()))) := by
  filter_upwards [P.lawConditionalRegret_kernel_limit_ae hw hc hH hbound h hh hb hm,
    ae_restrict_mem measurableSet_Ioo] with θ hL hθ
  have hθhalf : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := by constructor <;> linarith [hθ.1, hθ.2]
  have hLim := tendsto_finsetSum Finset.univ (fun i _ ↦
    P.lawConditionalRegret_integral_kernel_limit hw hc hH hbound h hh hb hm hθhalf i
      (hL.mono (fun ω hω ↦ hω i)))
  apply hLim.congr'
  exact Filter.Eventually.of_forall (fun δ ↦ by
    dsimp only
    rw [P.lawAdaptationRegret_eq_sum_conditional hw hc.le hbound h hh hb hm θ (θ + δ), Finset.sum_div])

end ProphetSecretary.Model
