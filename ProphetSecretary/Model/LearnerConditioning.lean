import ProphetSecretary.Model.EmpiricalConditionalValues

/-!
# Conditioning an actual learner on independent training data

The independent training law may differ from the online law. Fubini identifies
the expected objective with the average of the actual frozen policies, and
proves integrability of those conditional values. Freezing data is an analytical
operation; the online rule still uses only its observed training transcript.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n k : ℕ}

noncomputable def Learner.randomizedPolicyWithDataLaw (L : Learner n k)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D] : RandomizedPolicy n where
  Seed := Reservoir n k × L.Seed
  seedLaw := D
  rule := L.policy
  measurable_rule := L.policy_isMeasurable

def Instance.seedFirstWorld {A : Type*} (z : A × World n Unit) : World n A :=
  (z.2.1, (z.2.2.1, z.1))

lemma Instance.seedFirstWorld_measurePreserving {A : Type*} [MeasurableSpace A]
    (P : Instance n) (D : Measure A) [IsProbabilityMeasure D] :
    MeasurePreserving (@Instance.seedFirstWorld n A)
      (D.prod (P.worldLaw (Measure.dirac ()))) (P.worldLaw D) := by
  have h₀ := (measurePreserving_prodAssoc P.valuesLaw (Instance.clocksLaw n) (Measure.dirac ())).symm
    MeasurableEquiv.prodAssoc
  have h₁ := (MeasurePreserving.id D).prod h₀
  have h₂ := (MeasurePreserving.id D).prod
    (measurePreserving_fst (μ := P.valuesLaw.prod (Instance.clocksLaw n)) (ν := Measure.dirac ()))
  have h₃ := Measure.measurePreserving_swap (μ := D) (ν := P.valuesLaw.prod (Instance.clocksLaw n))
  have h₄ := measurePreserving_prodAssoc P.valuesLaw (Instance.clocksLaw n) D
  exact h₄.comp (h₃.comp (h₂.comp h₁))

lemma Learner.integrable_frozenExpectedReward (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D] :
    Integrable (fun d => (L.frozenRandomizedPolicy d.1 d.2).expectedReward P) D := by
  let π := L.randomizedPolicyWithDataLaw D
  have hmap := P.seedFirstWorld_measurePreserving D
  have hInt := hmap.integrable_comp_of_integrable (π.integrable_realizedReward P hP)
  have houter := hInt.integral_prod_left
  change Integrable (fun d => ∫ ω : World n Unit,
    π.realizedReward (Instance.seedFirstWorld (d, ω)) ∂P.worldLaw (Measure.dirac ())) D
  exact houter

lemma Learner.integrable_frozenExpectedDuration (L : Learner n k) (P : Instance n)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D] :
    Integrable (fun d => (L.frozenRandomizedPolicy d.1 d.2).expectedDuration P) D := by
  let π := L.randomizedPolicyWithDataLaw D
  have hmap := P.seedFirstWorld_measurePreserving D
  have hInt := hmap.integrable_comp_of_integrable (π.integrable_realizedDuration P)
  have houter := hInt.integral_prod_left
  change Integrable (fun d => ∫ ω : World n Unit,
    π.realizedDuration (Instance.seedFirstWorld (d, ω)) ∂P.worldLaw (Measure.dirac ())) D
  exact houter

theorem Learner.integral_frozenExpectedReward (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D] :
    (∫ d, (L.frozenRandomizedPolicy d.1 d.2).expectedReward P ∂D) =
      (L.randomizedPolicyWithDataLaw D).expectedReward P := by
  let π := L.randomizedPolicyWithDataLaw D
  have hmap := P.seedFirstWorld_measurePreserving D
  have hInt := hmap.integrable_comp_of_integrable (π.integrable_realizedReward P hP)
  have heq := integral_map (μ := D.prod (P.worldLaw (Measure.dirac ())))
    hmap.measurable.aemeasurable π.measurable_realizedReward.aestronglyMeasurable
  rw [hmap.map_eq] at heq
  have hprod := integral_prod
    (fun z : (Reservoir n k × L.Seed) × World n Unit =>
      L.policy.reward z.1 Finset.univ z.2.1 z.2.2.1) hInt
  exact hprod.symm.trans heq.symm

theorem Learner.integral_frozenExpectedDuration (L : Learner n k) (P : Instance n)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D] :
    (∫ d, (L.frozenRandomizedPolicy d.1 d.2).expectedDuration P ∂D) =
      (L.randomizedPolicyWithDataLaw D).expectedDuration P := by
  let π := L.randomizedPolicyWithDataLaw D
  have hmap := P.seedFirstWorld_measurePreserving D
  have hInt := hmap.integrable_comp_of_integrable (π.integrable_realizedDuration P)
  have heq := integral_map (μ := D.prod (P.worldLaw (Measure.dirac ())))
    hmap.measurable.aemeasurable π.measurable_realizedDuration.aestronglyMeasurable
  rw [hmap.map_eq] at heq
  have hprod := integral_prod
    (fun z : (Reservoir n k × L.Seed) × World n Unit =>
      L.policy.stoppingTime z.1 Finset.univ z.2.1 z.2.2.1) hInt
  exact hprod.symm.trans heq.symm

lemma Learner.integrable_frozenScalarObjective (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D] (w c : ℝ) :
    Integrable (fun d => (L.frozenRandomizedPolicy d.1 d.2).scalarObjective P w c) D := by
  have h := ((L.integrable_frozenExpectedReward P hP D).const_mul w).add
    ((L.integrable_frozenExpectedDuration P D).const_mul c)
  apply h.congr
  exact Filter.Eventually.of_forall fun d => (L.frozenRandomizedPolicy d.1 d.2).scalarObjective_eq P hP w c |>.symm

theorem Learner.integral_frozenScalarObjective (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D] (w c : ℝ) :
    (∫ d, (L.frozenRandomizedPolicy d.1 d.2).scalarObjective P w c ∂D) =
      (L.randomizedPolicyWithDataLaw D).scalarObjective P w c := by
  have heq : (∫ d, (L.frozenRandomizedPolicy d.1 d.2).scalarObjective P w c ∂D) =
      ∫ d, w * (L.frozenRandomizedPolicy d.1 d.2).expectedReward P +
        c * (L.frozenRandomizedPolicy d.1 d.2).expectedDuration P ∂D :=
    integral_congr_ae (Filter.Eventually.of_forall fun d =>
      (L.frozenRandomizedPolicy d.1 d.2).scalarObjective_eq P hP w c)
  rw [heq, integral_add ((L.integrable_frozenExpectedReward P hP D).const_mul w)
    ((L.integrable_frozenExpectedDuration P D).const_mul c), integral_const_mul, integral_const_mul,
    L.integral_frozenExpectedReward P hP D, L.integral_frozenExpectedDuration P D]
  exact ((L.randomizedPolicyWithDataLaw D).scalarObjective_eq P hP w c).symm

end ProphetSecretary.Model
