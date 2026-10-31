import ProphetSecretary.Limiting.HybridGeneratorVerification

/-!
# A finite potential residual under a different observation law

The policy executes under P, while target premiums use T and a target mark
law. These analytic target laws need not be the laws of the observations.
Individual and Poisson compensation are derived under the actual execution,
so original low-value histories remain available in mapped-reserve arguments.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma HybridRule.retainedDesignResidual_drift_under (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q T P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (hT : Integrable Model.Instance.maximum T.valuesLaw) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (π.retainedPotentialDrift Q T w c) ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) ∧
      Integrable (π.retainedDesignResidual Q T w c) (hybridWorldLaw P μ ν) ∧
      (∫ v, π.retainedDesignResidual Q T w c v ∂hybridWorldLaw P μ ν) =
        ∫ q, π.retainedPotentialDrift Q T w c q ∂(hybridWorldLaw P μ ν).prod Model.Instance.uniformClock := by
  have hQi (i : Fin n) := π.individualDesignPremium_compensation hπ Q P hQ (Q.law i)
    (Q.nonnegative i) (Q.integrable_maximum_iff.mp hQ i) μ ν hw hc i
  have hTi (i : Fin n) := π.individualDesignPremium_compensation hπ Q P hQ (T.law i)
    (T.nonnegative i) (T.integrable_maximum_iff.mp hT i) μ ν hw hc i
  have hRi (i : Fin n) : Integrable (fun v => π.reachedIndividualDesignPremium Q (Q.law i) w c i v -
      π.reachedIndividualDesignPremium Q (T.law i) w c i v) (hybridWorldLaw P μ ν) := (hQi i).1.sub (hTi i).1
  have hDi (i : Fin n) : Integrable (fun q => π.individualPotentialDrift Q (Q.law i) w c i q -
      π.individualPotentialDrift Q (T.law i) w c i q) ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) :=
    (hQi i).2.1.sub (hTi i).2.1
  have hDI : Integrable (π.retainedPotentialDrift Q T w c)
      ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) := integrable_finsetSum _ (fun i _ => hDi i)
  have hRI : Integrable (π.retainedDesignResidual Q T w c) (hybridWorldLaw P μ ν) :=
    (integrable_finsetSum _ (fun i _ => hRi i)).congr (Filter.Eventually.of_forall fun v =>
      (π.retainedDesignResidual_eq_premiumDifference Q T w c v).symm)
  refine ⟨hDI,hRI,?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall (π.retainedDesignResidual_eq_premiumDifference Q T w c)),
    integral_finsetSum _ (fun i _ => hRi i)]
  unfold HybridRule.retainedPotentialDrift
  rw [integral_finsetSum _ (fun i _ => hDi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sub (hQi i).1 (hTi i).1, integral_sub (hQi i).2.1 (hTi i).2.1,
    (hQi i).2.2,(hTi i).2.2,integral_prod _ (hQi i).2.1,integral_prod _ (hTi i).2.1]

lemma HybridRule.designResidual_generator_under (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q T P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (hT : Integrable Model.Instance.maximum T.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (π.designResidual Q T κ hκ w c) (hybridWorldLaw P μ ν) ∧
      Integrable (π.potentialGeneratorDrift Q T κ μ w c)
        ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) ∧
      (∫ v, π.designResidual Q T κ hκ w c v ∂hybridWorldLaw P μ ν) =
        ∫ q, π.potentialGeneratorDrift Q T κ μ w c q
          ∂(hybridWorldLaw P μ ν).prod Model.Instance.uniformClock := by
  have hR := π.retainedDesignResidual_drift_under hπ Q T P hQ hT μ ν hw hc
  have hPR := π.integrable_reachedPoissonPremium hπ P μ ν (designPoissonPremium Q κ w c)
    (measurable_designPoissonPremium Q hQ κ hI hw hc) (designPoissonPremium_le Q hQ κ hκ hI hw.le hc)
  have hPD := π.integrable_poissonPotentialDrift hπ Q P hQ κ hκ hI μ ν hw hc
  have hPE := π.poissonPremium_expectation_eq_drift hπ Q P hQ κ hκ hI μ ν hw hc
  have hDI : Integrable (π.designResidual Q T κ hκ w c) (hybridWorldLaw P μ ν) :=
    (hR.2.1.sub hPR).congr (Filter.Eventually.of_forall fun v =>
      (π.designResidual_eq_split Q T hQ κ hκ hw.le hc v).symm)
  refine ⟨hDI,hR.1.sub hPD,?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall (π.designResidual_eq_split Q T hQ κ hκ hw.le hc)),
    integral_sub hR.2.1 hPR,hR.2.2,hPE,← integral_prod _ hPD]
  exact (integral_sub hR.1 hPD).symm

end ProphetSecretary.Limiting
