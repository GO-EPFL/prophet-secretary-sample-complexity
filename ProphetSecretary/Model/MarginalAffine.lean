import ProphetSecretary.Model.MarginalResidual
import ProphetSecretary.Model.MarginalScorePremium
import ProphetSecretary.Probability.PolicyLikelihoodDerivative

/-!
# Exact one-marginal gain of a fixed canonical policy

Bellman residuals isolate the changed marginal. Replacing its latent value by
an independent base draw proves that the pending reach factor retains its base
law. The resulting affine payoff identity identifies the centered envelope
coordinate without differentiating a reoptimized policy.
-/

open MeasureTheory Set Filter
open scoped Classical Topology BigOperators

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem Instance.canonicalPayoff_singleMarginalTilt (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H)
    (i : Fin n) (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ᵐ a ∂P.law i, |h a| ≤ 1)
    (hm : ∫ a, h a ∂P.law i = 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    (P.valuePolicy hP hw.le hc).scalarObjective (P.singleMarginalTilt i h hh hb hm θ hθ) w c =
      optimalScalarValue P w c + θ * ∫ a, h a * P.marginalPremium hP hw hc i a ∂P.law i := by
  let Q := P.singleMarginalTilt i h hh hb hm θ hθ
  have hQ := Q.integrable_maximum_of_bounded (P.singleMarginalTilt_bounded i h hh hb hm θ hθ hbound)
  let C := P.valuePolicy hP hw.le hc
  let π : Policy Unit n := C.rule
  let F := P.reachedMarginalScorePremium hP hw hc i h
  have hRes := C.bellman_residualIdentity_split P Q hP hQ hw hc
  rw [P.valuePolicy_expectedDesignActionLoss_zero Q hP hw hc, add_zero] at hRes
  change optimalScalarValue P w c - C.scalarObjective Q w c =
    ∫ ω : World n Unit, π.reachedTransitionResidual P Q w c () ω.1 ω.2.1 ∂Q.worldLaw (Measure.dirac ()) at hRes
  have hPath (ω : World n Unit) (ht : ω.2.1 i ≤ 1) :
      π.reachedTransitionResidual P Q w c () ω.1 ω.2.1 = -θ * F ω := by
    unfold Policy.reachedTransitionResidual
    rw [Finset.sum_eq_single i]
    · rw [P.transitionResidual_singleMarginal_same hP i h hh hb hm hθ]
      change (if π.Reaches () ω.1 ω.2.1 i then -θ * P.marginalScorePremium w c i h ω.2.1 else 0) =
        -θ * (if ω.2.1 i ≤ 1 ∧ π.Reaches () ω.1 ω.2.1 i then P.marginalScorePremium w c i h ω.2.1 else 0)
      simp only [ht, true_and]
      split_ifs <;> ring
    · intro j _ hji
      rw [P.transitionResidual_singleMarginal_other i h hh hb hm hθ w c ω.2.1 hji]
      split_ifs <;> rfl
    · simp
  have hInt : (∫ ω : World n Unit, π.reachedTransitionResidual P Q w c () ω.1 ω.2.1 ∂Q.worldLaw (Measure.dirac ())) =
      -θ * ∫ ω : World n Unit, F ω ∂Q.worldLaw (Measure.dirac ()) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Q.world_clocks_mem_unitInterval (Measure.dirac ())] with ω hω
    exact hPath ω (hω i).2
  rw [hInt] at hRes
  have hInvariant : (∫ ω : World n Unit, F ω ∂Q.worldLaw (Measure.dirac ())) =
      ∫ ω : World n Unit, F ω ∂P.worldLaw (Measure.dirac ()) :=
    Q.integral_eq_of_replaceValue_invariant P (Measure.dirac ()) i
      (fun j hj ↦ P.singleMarginalTilt_law_other i h hh hb hm θ hθ hj) F
      (P.measurable_reachedMarginalScorePremium hP hw hc i h hh)
      (P.integrable_reachedMarginalScorePremium Q hP hw hc hH hbound i h hh hb)
      (P.reachedMarginalScorePremium_replaceValue hP hw hc i h)
  rw [hInvariant, P.mean_reachedMarginalScorePremium hP hw hc hH hbound i h hh hb] at hRes
  linarith

/-- The fixed-policy complete-vector score derivative equals the marginal
pairing with the actual acceptance-premium function. -/
theorem Instance.canonical_singleScore_derivative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H)
    (i : Fin n) (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ᵐ a ∂P.law i, |h a| ≤ 1)
    (hm : ∫ a, h a ∂P.law i = 0) :
    (P.valuePolicy hP hw.le hc).scalarLikelihoodDerivative P w c (singleScore i h) =
      ∫ a, h a * P.marginalPremium hP hw hc i a ∂P.law i := by
  let C := P.valuePolicy hP hw.le hc
  let L := ∫ a, h a * P.marginalPremium hP hw hc i a ∂P.law i
  have hAff : HasDerivAt (fun θ : ℝ ↦ optimalScalarValue P w c + θ * L) L 0 :=
    (hasDerivAt_mul_const (x := 0) L).const_add (optimalScalarValue P w c)
  have hActual : HasDerivAt (fun θ ↦ C.scalarObjective
      (P.likelihoodPath (singleScore i h) (singleScore_measurable i hh) (singleScore_bound P.law i hb)
        (singleScore_centered P.law i hm) θ) w c) L 0 := by
    apply hAff.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds (by norm_num : -(1 / 4 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 4)] with θ hθ
    rw [P.likelihoodPath_of_mem _ _ _ _ (abs_le.mpr hθ)]
    exact P.canonicalPayoff_singleMarginalTilt hP hw hc hH hbound i h hh hb hm (abs_le.mpr hθ)
  exact ((C.hasDerivAt_scalarObjective_likelihoodPath P hH hbound hw.le hc (singleScore i h)
    (singleScore_measurable i hh) (singleScore_bound P.law i hb) (singleScore_centered P.law i hm)).unique hActual)

end ProphetSecretary.Model
