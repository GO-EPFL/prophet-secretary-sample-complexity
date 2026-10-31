import ProphetSecretary.Limiting.Compensator

/-!
# Retained identities and anonymous Poisson arrivals

A hybrid rule sees each retained individual's identity and full observed history,
including zero-valued arrivals. Poisson observations are anonymous time/mark points.
Both decision functions are common to every realized Poisson count; generation labels
and the total point count do not occur in either callback's input type.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

variable {n N : ℕ} {Seed : Type*}

abbrev HybridWorld (n : ℕ) (Seed : Type*) := Configuration × ProphetSecretary.Model.World n Seed

noncomputable def hybridWorldLaw [MeasurableSpace Seed] (P : ProphetSecretary.Model.Instance n)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) : Measure (HybridWorld n Seed) :=
  worldLaw μ (P.worldLaw ν)

instance hybridWorldLaw_isProbability [MeasurableSpace Seed] (P : ProphetSecretary.Model.Instance n)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] : IsProbabilityMeasure (hybridWorldLaw P μ ν) := by
  unfold hybridWorldLaw
  infer_instance

structure HybridRule (n : ℕ) (Seed : Type*) where
  individual : Seed → ℝ → Fin n → ℝ → ProphetSecretary.Model.History n → Measure Point → Bool
  poisson : Seed → ℝ → ℝ → ProphetSecretary.Model.History n → Measure Point → Bool

def HybridRule.IsMeasurable [MeasurableSpace Seed] (π : HybridRule n Seed) : Prop :=
  Measurable (fun z : Seed × (ℝ × (Fin n × (ℝ × (ProphetSecretary.Model.History n × Measure Point)))) =>
    π.individual z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) ∧
  Measurable (fun z : Seed × (Point × (ProphetSecretary.Model.History n × Measure Point)) =>
    π.poisson z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2)

def retainedHistory (H : ProphetSecretary.Model.History (n + N)) : ProphetSecretary.Model.History n :=
  fun i => H (i.castAdd N)

noncomputable def poissonHistory (H : ProphetSecretary.Model.History (n + N)) : Measure Point :=
  ∑ j : Fin N, observationMeasure (H (j.natAdd n))

lemma measurable_retainedHistory (n N : ℕ) : Measurable (@retainedHistory n N) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (i.castAdd N))

lemma measurable_poissonHistory (n N : ℕ) : Measurable (@poissonHistory n N) :=
  Finset.measurable_fun_sum _ (fun j _ => measurable_observationMeasure.comp (measurable_pi_apply (j.natAdd n)))

noncomputable def HybridRule.asFinitePolicy (π : HybridRule n Seed) (N : ℕ) : ProphetSecretary.Model.Policy Seed (n + N) where
  decide r t j x H := Fin.addCases
    (fun i => π.individual r t i x (retainedHistory H) (poissonHistory H))
    (fun _ => π.poisson r t x (retainedHistory H) (poissonHistory H)) j

def combinedValues (x : Fin n → ℝ) (v : Fin N → Point) : Fin (n + N) → ℝ :=
  Fin.addCases x (fun j => (v j).2)

def combinedClocks (u : Fin n → ℝ) (v : Fin N → Point) : Fin (n + N) → ℝ :=
  Fin.addCases u (fun j => (v j).1)

lemma retainedHistory_history (x u : Fin n → ℝ) (v : Fin N → Point) (t : ℝ) :
    retainedHistory (ProphetSecretary.Model.history Finset.univ (combinedValues x v) (combinedClocks u v) t) =
      ProphetSecretary.Model.history Finset.univ x u t := by
  funext i
  simp [retainedHistory, ProphetSecretary.Model.history, combinedValues, combinedClocks]

lemma poissonHistory_history (x u : Fin n → ℝ) (v : Fin N → Point) (t : ℝ) :
    poissonHistory (ProphetSecretary.Model.history Finset.univ (combinedValues x v) (combinedClocks u v) t) =
      observedHistory (configurationMk N v) t := by
  unfold poissonHistory observedHistory
  apply Finset.sum_congr rfl
  intro j _
  simp only [ProphetSecretary.Model.history, Finset.mem_univ, true_and, combinedValues, combinedClocks,
    Fin.addCases_right, configurationMk]
  split_ifs <;> rfl

/-- The retained candidate receives its identity and every observed zero identity,
while the Poisson component contributes only its actually observed past points. -/
lemma HybridRule.individual_action (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (v : Fin N → Point) (i : Fin n) :
    (π.asFinitePolicy N).action r Finset.univ (combinedValues x v) (combinedClocks u v) (i.castAdd N) =
      π.individual r (u i) i (x i) (ProphetSecretary.Model.history Finset.univ x u (u i))
        (observedHistory (configurationMk N v) (u i)) := by
  unfold ProphetSecretary.Model.Policy.action HybridRule.asFinitePolicy
  dsimp only
  simp only [Fin.addCases_left, combinedValues, combinedClocks]
  rw [retainedHistory_history, poissonHistory_history]

lemma HybridRule.poisson_action (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (v : Fin N → Point) (j : Fin N) :
    (π.asFinitePolicy N).action r Finset.univ (combinedValues x v) (combinedClocks u v) (j.natAdd n) =
      π.poisson r (v j).1 (v j).2 (ProphetSecretary.Model.history Finset.univ x u (v j).1)
        (observedHistory (configurationMk N v) (v j).1) := by
  unfold ProphetSecretary.Model.Policy.action HybridRule.asFinitePolicy
  dsimp only
  simp only [Fin.addCases_right, combinedValues, combinedClocks]
  rw [retainedHistory_history, poissonHistory_history]

lemma HybridRule.individual_action_future_point (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (v : Fin N → Point) (i : Fin n) (p : Point) (hp : u i ≤ p.1) :
    (π.asFinitePolicy (N + 1)).action r Finset.univ (combinedValues x (Fin.snoc v p))
      (combinedClocks u (Fin.snoc v p)) (i.castAdd (N + 1)) =
      (π.asFinitePolicy N).action r Finset.univ (combinedValues x v) (combinedClocks u v) (i.castAdd N) := by
  rw [π.individual_action, π.individual_action]
  simp only [configurationMk]
  rw [observedHistory_snoc_of_future v p hp]

lemma HybridRule.poisson_action_future_point (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (v : Fin N → Point) (j : Fin N) (p : Point) (hp : (v j).1 ≤ p.1) :
    (π.asFinitePolicy (N + 1)).action r Finset.univ (combinedValues x (Fin.snoc v p))
      (combinedClocks u (Fin.snoc v p)) (j.castSucc.natAdd n) =
      (π.asFinitePolicy N).action r Finset.univ (combinedValues x v) (combinedClocks u v) (j.natAdd n) := by
  rw [π.poisson_action, π.poisson_action]
  simp only [Fin.snoc_castSucc, configurationMk]
  rw [observedHistory_snoc_of_future v p hp]

lemma HybridRule.asFinitePolicy_isMeasurable [MeasurableSpace Seed]
    (π : HybridRule n Seed) (hπ : π.IsMeasurable) (N : ℕ) : (π.asFinitePolicy N).IsMeasurable := by
  let Z := Seed × (ℝ × (ℝ × ProphetSecretary.Model.History (n + N)))
  have hr : Measurable (fun z : Z => z.1) := measurable_fst
  have ht : Measurable (fun z : Z => z.2.1) := measurable_fst.comp measurable_snd
  have hx : Measurable (fun z : Z => z.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hH : Measurable (fun z : Z => z.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hI := (measurable_retainedHistory n N).comp hH
  have hP := (measurable_poissonHistory n N).comp hH
  have hj (j : Fin (n + N)) : Measurable (fun z : Z => (π.asFinitePolicy N).decide z.1 z.2.1 j z.2.2.1 z.2.2.2) := by
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · unfold HybridRule.asFinitePolicy
      dsimp only
      simp only [Fin.addCases_left]
      exact hπ.1.comp (hr.prodMk (ht.prodMk ((measurable_const (a := i)).prodMk (hx.prodMk (hI.prodMk hP)))))
    · unfold HybridRule.asFinitePolicy
      dsimp only
      simp only [Fin.addCases_right]
      exact hπ.2.comp (hr.prodMk ((ht.prodMk hx).prodMk (hI.prodMk hP)))
  have hg : Measurable (fun z : Z × Fin (n + N) =>
      (π.asFinitePolicy N).decide z.1.1 z.1.2.1 z.2 z.1.2.2.1 z.1.2.2.2) :=
    measurable_from_prod_countable_left hj
  let Q := Seed × (ℝ × (Fin (n + N) × (ℝ × ProphetSecretary.Model.History (n + N))))
  have hm : Measurable (fun q : Q => ((q.1, (q.2.1, (q.2.2.2.1, q.2.2.2.2))), q.2.2.1)) := by fun_prop
  exact hg.comp hm

lemma measurable_combinedValues_family {Ω : Type*} [MeasurableSpace Ω]
    (x : Ω → Fin n → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i))
    (v : Ω → Fin N → Point) (hv : ∀ j, Measurable (fun ω => v ω j)) (k : Fin (n + N)) :
    Measurable (fun ω => combinedValues (x ω) (v ω) k) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [combinedValues, Fin.addCases_left] using hx i
  · simpa only [combinedValues, Fin.addCases_right, Function.comp_def] using measurable_snd.comp (hv j)

lemma measurable_combinedClocks_family {Ω : Type*} [MeasurableSpace Ω]
    (u : Ω → Fin n → ℝ) (hu : ∀ i, Measurable (fun ω => u ω i))
    (v : Ω → Fin N → Point) (hv : ∀ j, Measurable (fun ω => v ω j)) (k : Fin (n + N)) :
    Measurable (fun ω => combinedClocks (u ω) (v ω) k) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [combinedClocks, Fin.addCases_left] using hu i
  · simpa only [combinedClocks, Fin.addCases_right, Function.comp_def] using measurable_fst.comp (hv j)

noncomputable def HybridRule.stoppingTime (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) : ℝ :=
  (π.asFinitePolicy ω.1).stoppingTime r Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2)

noncomputable def HybridRule.realizedDuration (π : HybridRule n Seed) (v : HybridWorld n Seed) : ℝ :=
  π.stoppingTime v.2.2.2 v.2.1 v.2.2.1 v.1

def HybridRule.ReachesIndividual (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) (i : Fin n) : Prop :=
  (π.asFinitePolicy ω.1).Reaches r (combinedValues x ω.2) (combinedClocks u ω.2) (i.castAdd ω.1)

def HybridRule.ReachesPoisson (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) (j : Fin ω.1) : Prop :=
  (π.asFinitePolicy ω.1).Reaches r (combinedValues x ω.2) (combinedClocks u ω.2) (j.natAdd n)

lemma HybridRule.measurable_realizedDuration [MeasurableSpace Seed]
    (π : HybridRule n Seed) (hπ : π.IsMeasurable) : Measurable π.realizedDuration := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × ProphetSecretary.Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  exact (π.asFinitePolicy N).measurable_stoppingTime (π.asFinitePolicy_isMeasurable hπ N) hr
    (fun k => measurable_combinedValues_family _ hx _ hv k)
    (fun k => measurable_combinedClocks_family _ hu _ hv k) Finset.univ

lemma HybridRule.stoppingTime_le_one (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) : π.stoppingTime r x u ω ≤ 1 :=
  (π.asFinitePolicy ω.1).stoppingTime_le_one _ _ _ _

lemma HybridRule.realizedDuration_mem_unitInterval [MeasurableSpace Seed]
    (π : HybridRule n Seed) (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v : HybridWorld n Seed ∂hybridWorldLaw P μ ν, π.realizedDuration v ∈ Icc (0 : ℝ) 1 := by
  have hc := (Measure.quasiMeasurePreserving_fst (μ := configurationLaw μ) (ν := P.worldLaw ν)).ae
    (configuration_times_mem_Ioo μ)
  have hi := (Measure.quasiMeasurePreserving_snd (μ := configurationLaw μ) (ν := P.worldLaw ν)).ae
    (P.world_clocks_mem_unitInterval ν)
  filter_upwards [hc, hi] with v hv hvi
  have htime : ∀ k : Fin (n + v.1.1), 0 ≤ combinedClocks v.2.2.1 v.1.2 k := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa only [combinedClocks, Fin.addCases_left] using (hvi i).1
    · simpa only [combinedClocks, Fin.addCases_right] using (hv j).1.le
  exact ⟨(π.asFinitePolicy v.1.1).stoppingTime_nonneg _ _ _ _ htime,
    π.stoppingTime_le_one v.2.2.2 v.2.1 v.2.2.1 v.1⟩

lemma HybridRule.integrable_realizedDuration [MeasurableSpace Seed]
    (π : HybridRule n Seed) (hπ : π.IsMeasurable) (P : ProphetSecretary.Model.Instance n)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    Integrable π.realizedDuration (hybridWorldLaw P μ ν) := by
  apply Integrable.of_bound (π.measurable_realizedDuration hπ).aestronglyMeasurable 1
  filter_upwards [π.realizedDuration_mem_unitInterval P μ ν] with v hv
  simpa only [Real.norm_eq_abs, abs_of_nonneg hv.1] using hv.2

noncomputable def HybridRule.meanDuration [MeasurableSpace Seed] (π : HybridRule n Seed)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) : ℝ :=
  ∫ v, π.realizedDuration v ∂hybridWorldLaw P μ ν

lemma HybridRule.meanDuration_nonnegative [MeasurableSpace Seed] (π : HybridRule n Seed)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    0 ≤ π.meanDuration P μ ν := by
  apply integral_nonneg_of_ae
  exact (π.realizedDuration_mem_unitInterval P μ ν).mono (fun _ h => h.1)

lemma HybridRule.meanDuration_le_one [MeasurableSpace Seed] (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    π.meanDuration P μ ν ≤ 1 := by
  have he := integral_mono (π.integrable_realizedDuration hπ P μ ν) (integrable_const (1 : ℝ))
    (fun v : HybridWorld n Seed => π.stoppingTime_le_one v.2.2.2 v.2.1 v.2.2.1 v.1)
  simpa only [HybridRule.meanDuration, integral_const, probReal_univ, one_smul] using he

end ProphetSecretary.Limiting
