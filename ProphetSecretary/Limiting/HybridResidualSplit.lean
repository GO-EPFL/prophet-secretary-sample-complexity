import ProphetSecretary.Limiting.HybridDesignResidual
import ProphetSecretary.Limiting.FinitePotentialResidual
import ProphetSecretary.Limiting.RealCompensator

/-!
# Retained and anonymous parts of the design residual

Anonymous design marginals are zero. Their signed residual is the negative
positive-part premium at the current retained-state continuation value. The
retained transitions use the ordinary child-state residuals, with all retained
zero identities still observable to the competing rule.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*}

noncomputable def designPoissonPremium (Q : Model.Instance n) (κ : Measure ℝ) (w c : ℝ)
    (q : Point × Model.World n Seed) : ℝ :=
  Model.positivePremium κ w (poissonContinuation Q w c q.2.2.1 q.1.1)

noncomputable def HybridRule.retainedDesignResidual (π : HybridRule n Seed) (Q P : Model.Instance n)
    (w c : ℝ) (v : HybridWorld n Seed) : ℝ :=
  ∑ i : Fin n, if π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i then
    Q.transitionResidual P w c v.2.2.1 i else 0

lemma HybridRule.designResidual_eq_split (π : HybridRule n Seed) (Q P : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (v : HybridWorld n Seed) :
    π.designResidual Q P κ hκ w c v = π.retainedDesignResidual Q P w c v -
      π.reachedPoissonPremium (designPoissonPremium Q κ w c) v := by
  have hnn : ∀ q : Point × Model.World n Seed, 0 ≤ designPoissonPremium Q κ w c q :=
    fun _ => Model.positivePremium_nonnegative _ _ _
  rw [π.reachedPoissonPremium_eq_sum (designPoissonPremium Q κ w c) hnn v]
  unfold HybridRule.designResidual Model.Policy.reachedTransitionResidual HybridRule.retainedDesignResidual
  rw [Fin.sum_univ_add]
  simp_rw [appended_transitionResidual_individual Q P hQ κ hκ hw hc,
    appended_transitionResidual_poisson Q P hQ κ hκ hw hc]
  have hneg (j : Fin v.1.1) :
      (if (π.asFinitePolicy v.1.1).Reaches v.2.2.2 (combinedValues v.2.1 v.1.2)
          (combinedClocks v.2.2.1 v.1.2) (j.natAdd n)
        then -Model.positivePremium κ w (poissonContinuation Q w c v.2.2.1 (v.1.2 j).1) else 0) =
      -(if π.ReachesPoisson v.2.2.2 v.2.1 v.2.2.1 v.1 j then
        designPoissonPremium Q κ w c (v.1.2 j, v.2) else 0) := by
    unfold HybridRule.ReachesPoisson designPoissonPremium
    split_ifs <;> ring
  simp_rw [hneg]
  rw [Finset.sum_neg_distrib]
  rfl

lemma designPoissonPremium_nonnegative (Q : Model.Instance n) (κ : Measure ℝ) (w c : ℝ)
    (q : Point × Model.World n Seed) : 0 ≤ designPoissonPremium Q κ w c q :=
  Model.positivePremium_nonnegative _ _ _

lemma designPoissonPremium_le (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (q : Point × Model.World n Seed) :
    designPoissonPremium Q κ w c q ≤ w * ∫ x, x ∂κ :=
  Model.positivePremium_le_firstMoment κ hI hκ hw (poissonContinuation_nonnegative Q hQ hw hc _ _)

variable [MeasurableSpace Seed]

lemma measurable_designPoissonPremium (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hI : Integrable id κ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Measurable (@designPoissonPremium n Seed Q κ w c) := by
  have ht : Measurable (fun q : Point × Model.World n Seed => q.1.1) := by fun_prop
  have hH : Measurable (fun q : Point × Model.World n Seed =>
      Model.unseen (Model.history Finset.univ (fun _ => 0) q.2.2.1 q.1.1)) :=
    Model.measurable_unseen.comp (Model.measurable_history Finset.univ (fun _ => measurable_const)
      (fun i => (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))) ht)
  have hth := (measurable_poissonThreshold Q hQ hw.le hc).comp (hH.prodMk ht)
  have hv : Measurable (fun q : Point × Model.World n Seed => poissonContinuation Q w c q.2.2.1 q.1.1) := by
    convert hth.const_mul w using 1
    funext q
    unfold poissonContinuation poissonThreshold
    dsimp only [Function.comp_apply]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hw.ne']
  exact (Model.positivePremium_continuous κ hI w).measurable.comp hv

lemma HybridRule.integrable_retainedDesignResidual (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (π.retainedDesignResidual Q P w c) (hybridWorldLaw P μ ν) := by
  have hd := π.integrable_designResidual hπ Q P hQ hP κ hκ hI μ ν hw hc
  have hp := π.integrable_reachedPoissonPremium hπ P μ ν (designPoissonPremium Q κ w c)
    (measurable_designPoissonPremium Q hQ κ hI hw hc) (designPoissonPremium_le Q hQ κ hκ hI hw.le hc)
  apply (hd.add hp).congr
  exact Filter.Eventually.of_forall (fun v => by
    change π.designResidual Q P κ hκ w c v + π.reachedPoissonPremium (designPoissonPremium Q κ w c) v = _
    rw [π.designResidual_eq_split Q P hQ κ hκ hw.le hc v]
    ring)

end ProphetSecretary.Limiting
