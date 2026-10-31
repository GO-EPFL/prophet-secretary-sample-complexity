import ProphetSecretary.Probability.CandidateValue

/-!
# Weighted integration after independent coordinate replacement

A measurable event may use the complete online world. Replacing one value
coordinate and integrating the remaining randomness gives a concrete version
of its probability conditional on that value. This is an analytical operation;
it does not enlarge a policy's observation history.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def Instance.eventProbabilityAtValue (P : Instance n) (ν : Measure Seed)
    (E : Set (World n Seed)) (i : Fin n) (a : ℝ) : ℝ :=
  ∫ ω, if Instance.replaceValue i (ω, a) ∈ E then 1 else 0 ∂P.worldLaw ν

lemma Instance.measurable_eventProbabilityAtValue (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (E : Set (World n Seed)) (hE : MeasurableSet E) (i : Fin n) :
    Measurable (P.eventProbabilityAtValue ν E i) := by
  have hm : Measurable (fun z : World n Seed × ℝ =>
      if Instance.replaceValue i z ∈ E then (1 : ℝ) else 0) :=
    Measurable.ite ((P.replaceValue_measurePreserving ν i).measurable hE) measurable_const measurable_const
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

lemma Instance.eventProbabilityAtValue_mem_unit (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (E : Set (World n Seed)) (i : Fin n) (a : ℝ) :
    P.eventProbabilityAtValue ν E i a ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply integral_nonneg
    intro ω
    change (0 : ℝ) ≤ if Instance.replaceValue i (ω, a) ∈ E then 1 else 0
    split_ifs <;> norm_num
  · have hn := norm_integral_le_of_norm_le_const (μ := P.worldLaw ν)
      (f := fun ω => if Instance.replaceValue i (ω, a) ∈ E then (1 : ℝ) else 0)
      (Eventually.of_forall fun ω => by split_ifs <;> norm_num :
        ∀ᵐ ω ∂P.worldLaw ν, ‖if Instance.replaceValue i (ω, a) ∈ E then (1 : ℝ) else 0‖ ≤ 1)
    have ha : |P.eventProbabilityAtValue ν E i a| ≤ 1 := by
      simpa only [eventProbabilityAtValue, Real.norm_eq_abs, probReal_univ, mul_one] using hn
    exact (abs_le.mp ha).2

lemma Instance.integrable_eventProbabilityAtValue_weight (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (E : Set (World n Seed)) (hE : MeasurableSet E) (i : Fin n)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (hb : ∀ a, |ψ a| ≤ 1) :
    Integrable (fun a => P.eventProbabilityAtValue ν E i a * ψ a) (P.law i) := by
  apply Integrable.of_bound ((P.measurable_eventProbabilityAtValue ν E hE i).mul hψ).aestronglyMeasurable 1
  exact Eventually.of_forall fun a => by
    change ‖P.eventProbabilityAtValue ν E i a * ψ a‖ ≤ 1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (P.eventProbabilityAtValue_mem_unit ν E i a).1]
    exact (mul_le_mul (P.eventProbabilityAtValue_mem_unit ν E i a).2 (hb a)
      (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)

lemma Instance.integrable_event_value_weight (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (E : Set (World n Seed)) (hE : MeasurableSet E) (i : Fin n)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (hb : ∀ a, |ψ a| ≤ 1) :
    Integrable (fun ω : World n Seed => if ω ∈ E then ψ (ω.1 i) else 0) (P.worldLaw ν) := by
  apply Integrable.of_bound (Measurable.ite hE
    (hψ.comp ((measurable_pi_apply i).comp measurable_fst)) measurable_const).aestronglyMeasurable 1
  exact Eventually.of_forall fun ω => by
    change ‖if ω ∈ E then ψ (ω.1 i) else 0‖ ≤ 1
    split_ifs
    · simpa only [Real.norm_eq_abs] using hb (ω.1 i)
    · norm_num

/-- The marginal weighted integral is obtained from actual replacement and
Fubini, with no assumed conditional-distribution or independence interface. -/
theorem Instance.integral_event_value_weight (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (E : Set (World n Seed)) (hE : MeasurableSet E) (i : Fin n)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (hb : ∀ a, |ψ a| ≤ 1) :
    (∫ ω : World n Seed, if ω ∈ E then ψ (ω.1 i) else 0 ∂P.worldLaw ν) =
      ∫ a, P.eventProbabilityAtValue ν E i a * ψ a ∂P.law i := by
  let f : World n Seed → ℝ := fun ω => if ω ∈ E then ψ (ω.1 i) else 0
  have hf : Measurable f := Measurable.ite hE
    (hψ.comp ((measurable_pi_apply i).comp measurable_fst)) measurable_const
  have hfI : Integrable f (P.worldLaw ν) := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    exact Eventually.of_forall fun ω => by
      dsimp [f]
      split_ifs
      · simpa only [Real.norm_eq_abs] using hb (ω.1 i)
      · norm_num
  have hr := P.replaceValue_measurePreserving ν i
  have hrep := integral_map (μ := (P.worldLaw ν).prod (P.law i))
    hr.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hr.map_eq] at hrep
  calc
    _ = ∫ z, f (Instance.replaceValue i z) ∂(P.worldLaw ν).prod (P.law i) := hrep
    _ = ∫ a, (∫ ω, f (Instance.replaceValue i (ω, a)) ∂P.worldLaw ν) ∂P.law i :=
      integral_prod_symm _ (hr.integrable_comp_of_integrable hfI)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun a => by
        change (∫ ω, if Instance.replaceValue i (ω, a) ∈ E then
          ψ ((Function.update ω.1 i a) i) else 0 ∂P.worldLaw ν) = _
        simp only [Function.update_self]
        have heq : (fun ω : World n Seed => if Instance.replaceValue i (ω, a) ∈ E then ψ a else 0) =
            (fun ω => (if Instance.replaceValue i (ω, a) ∈ E then (1 : ℝ) else 0) * ψ a) := by
          funext ω
          split_ifs <;> simp
        rw [heq, integral_mul_const]
        rfl

lemma Policy.selectionProbabilityAtValue_eq_event (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) (i : Fin n) :
    π.selectionProbabilityAtValue P ν i =
      P.eventProbabilityAtValue ν {ω | π.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i} i := rfl

end ProphetSecretary.Model
