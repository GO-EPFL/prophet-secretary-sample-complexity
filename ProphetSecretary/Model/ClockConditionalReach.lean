import ProphetSecretary.Model.BellmanResidualBasic

/-!
# Reach conditional on the complete clock vector

Conditioning on all clocks is analytical: it does not supply future clocks to the policy.
The policy continues to act on its observed history. Integrating values and the independent
seed gives the clock-conditional reach weights used in `upstat:residual`.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def Policy.clockConditionalReach (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  (P.valuesLaw.prod ν).real {z : (Fin n → ℝ) × Seed | π.Reaches z.2 z.1 u i}

lemma Policy.measurableSet_clockReach (π : Policy Seed n) (hπ : π.IsMeasurable)
    (u : Fin n → ℝ) (i : Fin n) :
    MeasurableSet {z : (Fin n → ℝ) × Seed | π.Reaches z.2 z.1 u i} :=
  π.measurableSet_reaches hπ measurable_snd (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_const : Measurable (fun _ : (Fin n → ℝ) × Seed => u j))) i

lemma Policy.clockConditionalReach_nonnegative (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) (u : Fin n → ℝ) (i : Fin n) : 0 ≤ π.clockConditionalReach P ν u i :=
  ENNReal.toReal_nonneg

lemma Policy.clockConditionalReach_le_one (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (u : Fin n → ℝ) (i : Fin n) :
    π.clockConditionalReach P ν u i ≤ 1 := measureReal_le_one

/-- Reach weights decrease along the actual arrival order, even for policies using
all observed values, identities, zero observations, and independent randomness. -/
lemma Policy.clockConditionalReach_antitone_order (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (u : Fin n → ℝ) (i j : Fin n) (hij : u i ≤ u j) :
    π.clockConditionalReach P ν u j ≤ π.clockConditionalReach P ν u i := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro z hz
  exact hij.trans hz

lemma Policy.measurable_clockConditionalReach (π : Policy Seed n) (hπ : π.IsMeasurable) (P : Instance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Measurable (fun u : Fin n → ℝ => π.clockConditionalReach P ν u i) := by
  have hm : MeasurableSet {z : (Fin n → ℝ) × ((Fin n → ℝ) × Seed) |
      π.Reaches z.2.2 z.2.1 z.1 i} :=
    π.measurableSet_reaches hπ measurable_snd.snd
      (fun j => (measurable_pi_apply j).comp measurable_snd.fst)
      (fun j => (measurable_pi_apply j).comp measurable_fst) i
  exact (measurable_measure_prodMk_left (ν := P.valuesLaw.prod ν) hm).ennreal_toReal

/-- Reorder independent clocks, offers, and the original seed without changing their
laws. This identity is proved from product-measure associativity and symmetry. -/
def clockFirstWorld (z : (Fin n → ℝ) × ((Fin n → ℝ) × Seed)) : World n Seed :=
  (z.2.1, (z.1, z.2.2))

lemma Instance.clockFirstWorld_measurePreserving (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    MeasurePreserving clockFirstWorld ((Instance.clocksLaw n).prod (P.valuesLaw.prod ν)) (P.worldLaw ν) := by
  have h1 := (measurePreserving_prodAssoc (Instance.clocksLaw n) P.valuesLaw ν).symm MeasurableEquiv.prodAssoc
  have h2 := (Measure.measurePreserving_swap (μ := Instance.clocksLaw n) (ν := P.valuesLaw)).prod
    (MeasurePreserving.id ν)
  have h3 := measurePreserving_prodAssoc P.valuesLaw (Instance.clocksLaw n) ν
  exact h3.comp (h2.comp h1)

lemma Policy.integral_clockReach_indicator (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) (u : Fin n → ℝ) (i : Fin n) (b : ℝ) :
    (∫ z : (Fin n → ℝ) × Seed, if π.Reaches z.2 z.1 u i then b else 0 ∂P.valuesLaw.prod ν) =
      π.clockConditionalReach P ν u i * b := by
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, Policy.clockConditionalReach] using
    (integral_indicator_const b (π.measurableSet_clockReach hπ u i) (μ := P.valuesLaw.prod ν))

/-- Fubini supplies exactly the manuscript's conditional reach coefficients. No
independence between a data-selected design and its reach probabilities is inferred. -/
theorem Policy.integral_reachedTransitionResidual_eq_clockConditional
    (π : Policy Seed n) (hπ : π.IsMeasurable) (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ ω : World n Seed, π.reachedTransitionResidual Q P w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw ν) =
      ∫ u : Fin n → ℝ, ∑ i : Fin n, π.clockConditionalReach P ν u i * Q.transitionResidual P w c u i
        ∂Instance.clocksLaw n := by
  have hp := P.clockFirstWorld_measurePreserving ν
  have hm := π.measurable_reachedTransitionResidual hπ Q P hQ hP hw hc
    (measurable_snd.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))
  have hI : Integrable (fun z : (Fin n → ℝ) × ((Fin n → ℝ) × Seed) =>
      π.reachedTransitionResidual Q P w c z.2.2 z.2.1 z.1)
      ((Instance.clocksLaw n).prod (P.valuesLaw.prod ν)) :=
    hp.integrable_comp_of_integrable (π.integrable_reachedTransitionResidual hπ Q P hQ hP ν hw hc)
  have hmap := integral_map (μ := (Instance.clocksLaw n).prod (P.valuesLaw.prod ν))
    hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at hmap
  calc
    _ = ∫ z : (Fin n → ℝ) × ((Fin n → ℝ) × Seed),
        π.reachedTransitionResidual Q P w c z.2.2 z.2.1 z.1
          ∂(Instance.clocksLaw n).prod (P.valuesLaw.prod ν) := hmap
    _ = ∫ u : Fin n → ℝ, (∫ z : (Fin n → ℝ) × Seed,
        π.reachedTransitionResidual Q P w c z.2 z.1 u ∂P.valuesLaw.prod ν) ∂Instance.clocksLaw n :=
      integral_prod _ hI
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        change (∫ z : (Fin n → ℝ) × Seed,
          (∑ i : Fin n, if π.Reaches z.2 z.1 u i then Q.transitionResidual P w c u i else 0)
          ∂P.valuesLaw.prod ν) = ∑ i : Fin n, π.clockConditionalReach P ν u i * Q.transitionResidual P w c u i
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro i _
          exact π.integral_clockReach_indicator hπ P ν u i (Q.transitionResidual P w c u i)
        · intro i _
          have hm : Measurable (fun z : (Fin n → ℝ) × Seed =>
              if π.Reaches z.2 z.1 u i then Q.transitionResidual P w c u i else 0) :=
            Measurable.ite (π.measurableSet_clockReach hπ u i) measurable_const measurable_const
          apply Integrable.of_bound hm.aestronglyMeasurable |Q.transitionResidual P w c u i|
          exact Eventually.of_forall fun z => by split_ifs <;> simp [Real.norm_eq_abs]

lemma Policy.measurable_clockWeightedResidual (π : Policy Seed n) (hπ : π.IsMeasurable)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Measurable (fun u : Fin n → ℝ => ∑ i : Fin n,
      π.clockConditionalReach P ν u i * Q.transitionResidual P w c u i) := by
  apply Finset.measurable_sum
  intro i _
  exact (π.measurable_clockConditionalReach hπ P ν i).mul
    (Q.measurable_transitionResidual P hQ hP hw hc (u := id) (fun j => measurable_pi_apply j) i)

lemma Policy.integrable_clockWeightedResidual (π : Policy Seed n) (hπ : π.IsMeasurable)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (fun u : Fin n → ℝ => ∑ i : Fin n,
      π.clockConditionalReach P ν u i * Q.transitionResidual P w c u i) (Instance.clocksLaw n) := by
  apply integrable_finsetSum
  intro i _
  have hm := (π.measurable_clockConditionalReach hπ P ν i).mul
    (Q.measurable_transitionResidual P hQ hP hw hc (u := id) (fun j => measurable_pi_apply j) i)
  apply Integrable.of_bound hm.aestronglyMeasurable
    (w * ((∫ x, x ∂Q.law i) + ∫ x, x ∂P.law i))
  exact Eventually.of_forall fun u => by
    change ‖π.clockConditionalReach P ν u i * Q.transitionResidual P w c u i‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (π.clockConditionalReach_nonnegative P ν u i)]
    exact (mul_le_mul (π.clockConditionalReach_le_one P ν u i)
      (Q.abs_transitionResidual_le P hQ hP hw.le hc u i) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

end ProphetSecretary.Model
