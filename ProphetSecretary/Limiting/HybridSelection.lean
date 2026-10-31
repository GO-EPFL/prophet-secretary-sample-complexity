import ProphetSecretary.Limiting.HybridReach

/-!
# Selection of a retained identity in a hybrid execution

Selection is the actual first accepted occurrence, with the existing null-tie
identity convention on each finite configuration. Every event and indicator
is defined from the same count-hidden hybrid rule, with no new observation.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*}

def HybridRule.SelectsIndividual (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) (i : Fin n) : Prop :=
  (π.asFinitePolicy ω.1).ActualSelects r Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) (i.castAdd ω.1)

noncomputable def HybridRule.retainedSelectionIndicator (π : HybridRule n Seed) (i : Fin n)
    (v : HybridWorld n Seed) : ℝ :=
  if π.SelectsIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i then 1 else 0

lemma HybridRule.duration_eq_clock_of_selectsIndividual (π : HybridRule n Seed) (i : Fin n)
    (v : HybridWorld n Seed) (hs : π.SelectsIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i) :
    π.realizedDuration v = v.2.2.1 i := by
  have h := hs.1.2
  simpa only [HybridRule.realizedDuration,HybridRule.stoppingTime,combinedClocks,Fin.addCases_left] using h.symm

variable [MeasurableSpace Seed]

lemma HybridRule.measurable_retainedSelectionIndicator (π : HybridRule n Seed) (hπ : π.IsMeasurable) (i : Fin n) :
    Measurable (π.retainedSelectionIndicator i) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hx (j : Fin n) : Measurable (fun v : Ω => v.2.1 j) := (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  have hu (j : Fin n) : Measurable (fun v : Ω => v.2.2.1 j) :=
    (measurable_pi_apply j).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  exact Measurable.ite ((π.asFinitePolicy N).measurableSet_actualSelects
    (π.asFinitePolicy_isMeasurable hπ N) hr
    (fun k => measurable_combinedValues_family _ hx _ hv k)
    (fun k => measurable_combinedClocks_family _ hu _ hv k) Finset.univ (i.castAdd N)) measurable_const measurable_const

lemma HybridRule.measurableSet_selectsIndividual (π : HybridRule n Seed) (hπ : π.IsMeasurable) (i : Fin n) :
    MeasurableSet {v : HybridWorld n Seed | π.SelectsIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i} := by
  have heq : {v : HybridWorld n Seed | π.SelectsIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i} =
      {v | π.retainedSelectionIndicator i v = 1} := by
    ext v
    change _ ↔ (if _ then (1 : ℝ) else 0) = 1
    split_ifs <;> simp_all
  rw [heq]
  exact measurableSet_eq_fun (π.measurable_retainedSelectionIndicator hπ i) measurable_const

noncomputable def HybridRule.individualSelectionProbability (π : HybridRule n Seed) (P : Model.Instance n)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) (i : Fin n) : ℝ :=
  (hybridWorldLaw P μ ν).real {v : HybridWorld n Seed | π.SelectsIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i}

omit [MeasurableSpace Seed] in
lemma HybridRule.retainedSelectionIndicator_mem_unit (π : HybridRule n Seed) (i : Fin n) (v : HybridWorld n Seed) :
    π.retainedSelectionIndicator i v ∈ Icc (0 : ℝ) 1 := by
  unfold HybridRule.retainedSelectionIndicator
  split_ifs <;> norm_num

lemma HybridRule.integrable_retainedSelectionIndicator (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Integrable (π.retainedSelectionIndicator i) (hybridWorldLaw P μ ν) := by
  apply Integrable.of_bound (π.measurable_retainedSelectionIndicator hπ i).aestronglyMeasurable 1
  exact Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs,abs_of_nonneg (π.retainedSelectionIndicator_mem_unit i v).1]
    exact (π.retainedSelectionIndicator_mem_unit i v).2

lemma HybridRule.integral_retainedSelectionIndicator (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (∫ v, π.retainedSelectionIndicator i v ∂hybridWorldLaw P μ ν) = π.individualSelectionProbability P μ ν i := by
  simpa only [HybridRule.retainedSelectionIndicator,HybridRule.individualSelectionProbability,
    Set.indicator_apply,Set.mem_setOf_eq,Pi.one_apply] using
      (integral_indicator_one (μ := hybridWorldLaw P μ ν) (π.measurableSet_selectsIndividual hπ i))

end ProphetSecretary.Limiting
