import ProphetSecretary.Probability.CoordinateResponse
import ProphetSecretary.Model.ProphetWinner
import ProphetSecretary.Model.ValuePerturbationSupport

/-!
# Marginal representations of selection and prophet responses

The functions aᵢ and bᵢ in `upmom:tv` are concrete probabilities obtained by
replacing the candidate value and integrating every other independent input.
They are measurable and lie in [0,1]. Their weighted integrals recover the
actual selected response and the full-vector prophet response.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def Instance.prophetProbabilityAtValue (P : Instance n) (ν : Measure Seed)
    (i : Fin n) : ℝ → ℝ :=
  P.eventProbabilityAtValue ν {ω | ProphetWins ω.1 i} i

/-- The auxiliary seed and clocks integrate out of the prophet probability. -/
lemma Instance.prophetProbabilityAtValue_eq_valuesIntegral (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) (a : ℝ) :
    P.prophetProbabilityAtValue ν i a =
      ∫ x, if ProphetWins (Function.update x i a) i then (1 : ℝ) else 0 ∂P.valuesLaw := by
  change (∫ ω : World n Seed, (if ProphetWins (Function.update ω.1 i a) i then (1 : ℝ) else 0)
    ∂P.valuesLaw.prod ((Instance.clocksLaw n).prod ν)) = _
  simpa only [probReal_univ, one_smul] using
    (integral_fun_fst (μ := P.valuesLaw) (ν := (Instance.clocksLaw n).prod ν)
      (fun x : Fin n → ℝ => if ProphetWins (Function.update x i a) i then (1 : ℝ) else 0))

lemma Instance.measurable_prophetProbabilityAtValue (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) : Measurable (P.prophetProbabilityAtValue ν i) :=
  P.measurable_eventProbabilityAtValue ν _ (measurable_fst (measurableSet_prophetWins i)) i

lemma Instance.prophetProbabilityAtValue_mem_unit (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) (a : ℝ) :
    P.prophetProbabilityAtValue ν i a ∈ Icc (0 : ℝ) 1 :=
  P.eventProbabilityAtValue_mem_unit ν _ i a

lemma Policy.selectionProbabilityAtValue_mem_unit (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) (a : ℝ) :
    π.selectionProbabilityAtValue P ν i a ∈ Icc (0 : ℝ) 1 :=
  P.eventProbabilityAtValue_mem_unit ν {ω | π.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i} i a

/-- Selection probabilities conditional on the candidate's value integrate to
the fixed policy's response, retaining all zero-valued observation histories. -/
theorem RandomizedPolicy.selectedResponse_eq_marginal_integrals (π : RandomizedPolicy n)
    (P : Instance n) (ψ : Fin n → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i))
    (hb : ∀ i a, |ψ i a| ≤ 1) :
    π.selectedResponse P ψ = ∑ i, ∫ a,
      π.rule.selectionProbabilityAtValue P π.seedLaw i a * ψ i a ∂P.law i := by
  have hm (i : Fin n) : MeasurableSet {ω : π.World |
      π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i} :=
    π.rule.measurableSet_actualSelects π.measurable_rule
      (measurable_snd.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) Finset.univ i
  have hI (i : Fin n) : Integrable (fun ω : π.World =>
      if π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i then ψ i (ω.1 i) else 0)
      (P.worldLaw π.seedLaw) :=
    P.integrable_event_value_weight π.seedLaw _ (hm i) i (ψ i) (hψ i) (hb i)
  unfold selectedResponse Policy.mappedReward
  rw [integral_finsetSum _ (fun i _ => hI i)]
  apply Finset.sum_congr rfl
  intro i _
  exact P.integral_event_value_weight π.seedLaw _ (hm i) i (ψ i) (hψ i) (hb i)

/-- Prophet conditioning uses only an analytical full-vector event. The seed
is independent and integrated out, and the maximum-zero response is zero. -/
theorem Instance.expectedProphetResponse_eq_marginal_integrals (P : Instance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) (hb : ∀ i a, |ψ i a| ≤ 1) :
    P.expectedProphetResponse ψ = ∑ i, ∫ a,
      P.prophetProbabilityAtValue ν i a * ψ i a ∂P.law i := by
  have hproj : MeasurePreserving (fun ω : World n Seed => ω.1) (P.worldLaw ν) P.valuesLaw :=
    measurePreserving_fst
  have heq := integral_map (μ := P.worldLaw ν) hproj.measurable.aemeasurable
    (measurable_prophetResponse ψ hψ).aestronglyMeasurable
  rw [hproj.map_eq] at heq
  have hm (i : Fin n) : MeasurableSet {ω : World n Seed | ProphetWins ω.1 i} :=
    measurable_fst (measurableSet_prophetWins i)
  change (∫ x, prophetResponse ψ x ∂P.valuesLaw) = _
  rw [heq]
  simp only [prophetResponse]
  have hI (i : Fin n) : Integrable (fun ω : World n Seed =>
      if ProphetWins ω.1 i then ψ i (ω.1 i) else 0) (P.worldLaw ν) :=
    P.integrable_event_value_weight ν _ (hm i) i (ψ i) (hψ i) (hb i)
  rw [integral_finsetSum _ (fun i _ => hI i)]
  apply Finset.sum_congr rfl
  intro i _
  exact P.integral_event_value_weight ν _ (hm i) i (ψ i) (hψ i) (hb i)

/-- A weighted response difference is the sum of its marginal signed densities. -/
theorem RandomizedPolicy.response_difference_eq_marginal_integrals (π : RandomizedPolicy n)
    (P : Instance n) (ψ : Fin n → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i))
    (hb : ∀ i a, |ψ i a| ≤ 1) (C : ℝ) :
    π.selectedResponse P ψ - C * P.expectedProphetResponse ψ =
      ∑ i, ∫ a, (π.rule.selectionProbabilityAtValue P π.seedLaw i a -
        C * P.prophetProbabilityAtValue π.seedLaw i a) * ψ i a ∂P.law i := by
  rw [π.selectedResponse_eq_marginal_integrals P ψ hψ hb,
    P.expectedProphetResponse_eq_marginal_integrals π.seedLaw ψ hψ hb,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hm : MeasurableSet {ω : π.World | π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i} :=
    π.rule.measurableSet_actualSelects π.measurable_rule (by fun_prop)
      (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i
  have ha := P.integrable_eventProbabilityAtValue_weight π.seedLaw _ hm i (ψ i) (hψ i) (hb i)
  have hbp := P.integrable_eventProbabilityAtValue_weight π.seedLaw _
    (measurable_fst (measurableSet_prophetWins i)) i (ψ i) (hψ i) (hb i)
  change Integrable (fun a => π.rule.selectionProbabilityAtValue P π.seedLaw i a * ψ i a) (P.law i) at ha
  change Integrable (fun a => P.prophetProbabilityAtValue π.seedLaw i a * ψ i a) (P.law i) at hbp
  have heq : (fun a => (π.rule.selectionProbabilityAtValue P π.seedLaw i a -
        C * P.prophetProbabilityAtValue π.seedLaw i a) * ψ i a) =
      (fun a => π.rule.selectionProbabilityAtValue P π.seedLaw i a * ψ i a -
        C * (P.prophetProbabilityAtValue π.seedLaw i a * ψ i a)) := by
    funext a
    ring
  rw [heq, integral_sub ha (hbp.const_mul C), integral_const_mul]

end ProphetSecretary.Model
