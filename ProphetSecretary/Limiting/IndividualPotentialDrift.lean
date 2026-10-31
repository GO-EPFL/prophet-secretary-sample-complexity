import ProphetSecretary.Limiting.HybridIndividualCompensatorReal
import ProphetSecretary.Limiting.HybridResidualSplit

/-!
# Compensating an individual continuation premium

The premium uses the finite design's child state at the candidate time.
Erasing and then reinstalling that clock leaves the child continuation exactly
unchanged. The resulting hazard identity is derived from the actual hybrid
execution, including its retained zero observations and anonymous arrivals.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def individualDesignPremium (Q : Model.Instance n) (κ : Measure ℝ)
    (w c : ℝ) (i : Fin n) (q : ℝ × HybridWorld n Seed) : ℝ :=
  Model.positivePremium κ w (Q.continuationAtArrival w c (fun _ => 0)
    (Function.update q.2.2.2.1 i q.1) i)

lemma measurable_individualDesignPremium (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hI : Integrable id κ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) :
    Measurable (@individualDesignPremium n Seed Q κ w c i) := by
  have hu (j : Fin n) : Measurable (fun q : ℝ × HybridWorld n Seed => (Function.update q.2.2.2.1 i q.1) j) := by
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self] using (measurable_fst : Measurable (fun q : ℝ × HybridWorld n Seed => q.1))
    · have hm : Measurable (fun q : ℝ × HybridWorld n Seed => q.2.2.2.1 j) := by fun_prop
      simpa only [Function.update_of_ne hj] using hm
  exact (Model.positivePremium_continuous κ hI w).measurable.comp
    (Q.measurable_continuationAtArrival hQ hw hc (fun _ => measurable_const) hu i)

omit [MeasurableSpace Seed] in
lemma individualDesignPremium_nonnegative (Q : Model.Instance n) (κ : Measure ℝ)
    (w c : ℝ) (i : Fin n) (q : ℝ × HybridWorld n Seed) : 0 ≤ individualDesignPremium Q κ w c i q :=
  Model.positivePremium_nonnegative _ _ _

omit [MeasurableSpace Seed] in
lemma individualDesignPremium_le (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ a ∂κ, 0 ≤ a) (hI : Integrable id κ) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (i : Fin n) (q : ℝ × HybridWorld n Seed) :
    individualDesignPremium Q κ w c i q ≤ w * ∫ x, x ∂κ :=
  Model.positivePremium_le_firstMoment κ hI hκ hw
    (Q.continuationAtArrival_nonnegative hQ hw hc _ _ _)

omit [MeasurableSpace Seed] in
lemma individualDesignPremium_erase (Q : Model.Instance n) (κ : Measure ℝ)
    (w c : ℝ) (i : Fin n) (t : ℝ) (v : HybridWorld n Seed) :
    individualDesignPremium Q κ w c i (t, eraseIndividualClock i v) =
      individualDesignPremium Q κ w c i (t,v) := by
  simp only [individualDesignPremium, eraseIndividualClock, Model.Instance.eraseClock, Model.Instance.replaceClock, Function.update_idem]

omit [MeasurableSpace Seed] in
lemma individualDesignPremium_atArrival (Q : Model.Instance n) (κ : Measure ℝ)
    (w c : ℝ) (i : Fin n) (v : HybridWorld n Seed) :
    individualDesignPremium Q κ w c i (v.2.2.1 i, eraseIndividualClock i v) =
      Model.positivePremium κ w (Q.continuationAtArrival w c v.2.1 v.2.2.1 i) := by
  rw [individualDesignPremium_erase]
  simp only [individualDesignPremium, Function.update_eq_self]
  rw [Q.continuationAtArrival_values_invariant w c (fun _ => 0) v.2.1]

noncomputable def HybridRule.reachedIndividualDesignPremium (π : HybridRule n Seed)
    (Q : Model.Instance n) (κ : Measure ℝ) (w c : ℝ) (i : Fin n) (v : HybridWorld n Seed) : ℝ :=
  if π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i then
    Model.positivePremium κ w (Q.continuationAtArrival w c v.2.1 v.2.2.1 i) else 0

noncomputable def HybridRule.individualPotentialDrift (π : HybridRule n Seed)
    (Q : Model.Instance n) (κ : Measure ℝ) (w c : ℝ) (i : Fin n) (q : HybridWorld n Seed × ℝ) : ℝ :=
  if q.2 ≤ π.realizedDuration q.1 ∧ q.2 < q.1.2.2.1 i then
    individualDesignPremium Q κ w c i (q.2,q.1) / (1 - q.2) else 0

lemma HybridRule.individualDesignPremium_compensation (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ a ∂κ, 0 ≤ a) (hI : Integrable id κ)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) :
    Integrable (π.reachedIndividualDesignPremium Q κ w c i) (hybridWorldLaw P μ ν) ∧
      Integrable (π.individualPotentialDrift Q κ w c i) ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) ∧
      (∫ v, π.reachedIndividualDesignPremium Q κ w c i v ∂hybridWorldLaw P μ ν) =
        ∫ v, ∫ t, π.individualPotentialDrift Q κ w c i (v,t)
          ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ ν := by
  have h := π.individual_compensator_real hπ i P μ ν (individualDesignPremium Q κ w c i)
    (measurable_individualDesignPremium Q hQ κ hI hw hc i)
    (individualDesignPremium_nonnegative Q κ w c i) (individualDesignPremium_le Q hQ κ hκ hI hw.le hc i)
  have hR : HybridRule.realIndividualReachedPremium π i (individualDesignPremium Q κ w c i) =
      π.reachedIndividualDesignPremium Q κ w c i := by
    funext v
    rw [HybridRule.realIndividualReachedPremium, individualDesignPremium_atArrival]
    simp only [HybridRule.reachedIndividualDesignPremium, HybridRule.ReachesIndividual, Model.Policy.Reaches,
      HybridRule.realizedDuration, HybridRule.stoppingTime, combinedClocks, Fin.addCases_left]
    rfl
  have hD : HybridRule.realIndividualStoppedHazard π i (individualDesignPremium Q κ w c i) =
      π.individualPotentialDrift Q κ w c i := by
    funext q
    simp only [HybridRule.realIndividualStoppedHazard, HybridRule.individualPotentialDrift,
      individualDesignPremium_erase]
  rw [hR, hD] at h
  exact h

end ProphetSecretary.Limiting
