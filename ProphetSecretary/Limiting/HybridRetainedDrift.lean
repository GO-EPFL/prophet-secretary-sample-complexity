import ProphetSecretary.Limiting.IndividualPotentialDrift

/-!
# The retained part of the finite-potential generator

Both the design and evaluation premiums are compensated separately, so their
signed residual has the actual stopped individual-clock hazard representation.
All retained histories, including zero-valued arrivals, remain observable.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def HybridRule.retainedPotentialDrift (π : HybridRule n Seed)
    (Q P : Model.Instance n) (w c : ℝ) (q : HybridWorld n Seed × ℝ) : ℝ :=
  ∑ i, (π.individualPotentialDrift Q (Q.law i) w c i q - π.individualPotentialDrift Q (P.law i) w c i q)

omit [MeasurableSpace Seed] in
lemma HybridRule.retainedDesignResidual_eq_premiumDifference (π : HybridRule n Seed)
    (Q P : Model.Instance n) (w c : ℝ) (v : HybridWorld n Seed) :
    π.retainedDesignResidual Q P w c v = ∑ i,
      (π.reachedIndividualDesignPremium Q (Q.law i) w c i v -
        π.reachedIndividualDesignPremium Q (P.law i) w c i v) := by
  unfold HybridRule.retainedDesignResidual
  apply Finset.sum_congr rfl
  intro i _
  unfold HybridRule.reachedIndividualDesignPremium Model.Instance.transitionResidual Model.Instance.lawResidual
  rw [Q.continuationAtArrival_values_invariant w c v.2.1 (fun _ => 0)]
  split_ifs <;> ring

lemma HybridRule.retainedDesignResidual_expectation_eq_drift (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (π.retainedPotentialDrift Q P w c) ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) ∧
      (∫ v, π.retainedDesignResidual Q P w c v ∂hybridWorldLaw P μ ν) =
        ∫ v, ∫ t, π.retainedPotentialDrift Q P w c (v,t)
          ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ ν := by
  have hQi (i : Fin n) := π.individualDesignPremium_compensation hπ Q P hQ (Q.law i)
    (Q.nonnegative i) (Q.integrable_maximum_iff.mp hQ i) μ ν hw hc i
  have hPi (i : Fin n) := π.individualDesignPremium_compensation hπ Q P hQ (P.law i)
    (P.nonnegative i) (P.integrable_maximum_iff.mp hP i) μ ν hw hc i
  have hRi (i : Fin n) : Integrable (fun v =>
      π.reachedIndividualDesignPremium Q (Q.law i) w c i v -
        π.reachedIndividualDesignPremium Q (P.law i) w c i v) (hybridWorldLaw P μ ν) :=
    (hQi i).1.sub (hPi i).1
  have hDi (i : Fin n) : Integrable (fun q =>
      π.individualPotentialDrift Q (Q.law i) w c i q -
        π.individualPotentialDrift Q (P.law i) w c i q)
      ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) := (hQi i).2.1.sub (hPi i).2.1
  have hI : Integrable (π.retainedPotentialDrift Q P w c)
      ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) :=
    integrable_finsetSum _ (fun i _ => hDi i)
  refine ⟨hI, ?_⟩
  rw [← integral_prod _ hI]
  have hfun := fun v : HybridWorld n Seed => π.retainedDesignResidual_eq_premiumDifference Q P w c v
  rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
  rw [integral_finsetSum _ (fun i _ => hRi i)]
  unfold HybridRule.retainedPotentialDrift
  rw [integral_finsetSum _ (fun i _ => hDi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sub (hQi i).1 (hPi i).1, integral_sub (hQi i).2.1 (hPi i).2.1,
    (hQi i).2.2, (hPi i).2.2, integral_prod _ (hQi i).2.1, integral_prod _ (hPi i).2.1]

end ProphetSecretary.Limiting
