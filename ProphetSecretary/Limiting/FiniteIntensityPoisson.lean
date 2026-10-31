import ProphetSecretary.Limiting.PoissonCountMoments
import ProphetSecretary.Model.Instance
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite-intensity marked Poisson offers

The actual complete point configuration has a Poisson number of iid uniform-time,
normalized-mark pairs. Its finite array is analytical data. One anonymous online rule
observes the current time and mark and the counting measure of past observations;
neither the realized total count nor generation labels occur in its input type.

Here the mark intensity is a finite measure.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

abbrev Point := ℝ × ℝ
abbrev Configuration := Σ N : ℕ, Fin N → Point
abbrev World (Seed : Type*) := Configuration × Seed

def configurationMk (N : ℕ) (v : Fin N → Point) : Configuration := ⟨N, v⟩

lemma measurable_configuration_mk (N : ℕ) : Measurable (configurationMk N) :=
  Measurable.of_le_map (iInf_le _ N)

lemma measurable_of_configuration_branches {β : Type*} [MeasurableSpace β]
    (f : Configuration → β) (hf : ∀ N, Measurable (fun v : Fin N → Point => f ⟨N, v⟩)) : Measurable f := by
  intro S hS
  change MeasurableSet[⨅ N : ℕ, (inferInstance : MeasurableSpace (Fin N → Point)).map (configurationMk N)] (f ⁻¹' S)
  rw [MeasurableSpace.measurableSet_iInf]
  exact fun N => hf N hS

noncomputable def pointLaw (μ : FiniteMeasure ℝ) : Measure Point :=
  ProphetSecretary.Model.Instance.uniformClock.prod (μ.normalize : Measure ℝ)

instance pointLaw_isProbability (μ : FiniteMeasure ℝ) : IsProbabilityMeasure (pointLaw μ) := by
  unfold pointLaw
  infer_instance

noncomputable def arrayLaw (μ : FiniteMeasure ℝ) (N : ℕ) : Measure (Fin N → Point) :=
  Measure.pi (fun _ : Fin N => pointLaw μ)

instance arrayLaw_isProbability (μ : FiniteMeasure ℝ) (N : ℕ) : IsProbabilityMeasure (arrayLaw μ N) := by
  unfold arrayLaw
  infer_instance

noncomputable def fiberLaw (μ : FiniteMeasure ℝ) (N : ℕ) : Measure Configuration :=
  (arrayLaw μ N).map (configurationMk N)

instance fiberLaw_isProbability (μ : FiniteMeasure ℝ) (N : ℕ) : IsProbabilityMeasure (fiberLaw μ N) := by
  constructor
  rw [fiberLaw, Measure.map_apply (measurable_configuration_mk N) MeasurableSet.univ]
  simp

/-- The law contains exactly the actual finite point array, including points after
stopping. There are no infinitely many unused marks in this likelihood space. -/
noncomputable def configurationLaw (μ : FiniteMeasure ℝ) : Measure Configuration :=
  Measure.sum (fun N : ℕ => ENNReal.ofReal (poissonWeight μ.mass N) • fiberLaw μ N)

lemma measurable_configuration_count : Measurable (fun ω : Configuration => ω.1) :=
  measurable_of_configuration_branches _ (fun _ => measurable_const)

lemma fiberLaw_count_map (μ : FiniteMeasure ℝ) (N : ℕ) :
    (fiberLaw μ N).map (fun ω : Configuration => ω.1) = Measure.dirac N := by
  rw [fiberLaw, Measure.map_map measurable_configuration_count (measurable_configuration_mk N)]
  change (arrayLaw μ N).map (fun _ => N) = Measure.dirac N
  simp only [Measure.map_const, measure_univ, one_smul]

lemma configurationLaw_count_map (μ : FiniteMeasure ℝ) :
    (configurationLaw μ).map (fun ω : Configuration => ω.1) = poissonMeasure μ.mass := by
  rw [configurationLaw, Measure.map_sum measurable_configuration_count.aemeasurable]
  simp_rw [Measure.map_smul, fiberLaw_count_map]
  rfl

instance configurationLaw_isProbability (μ : FiniteMeasure ℝ) : IsProbabilityMeasure (configurationLaw μ) := by
  constructor
  have h := congrArg (fun m : Measure ℕ => m univ) (configurationLaw_count_map μ)
  simpa only [Measure.map_apply measurable_configuration_count MeasurableSet.univ, Set.preimage_univ,
    measure_univ] using h

lemma configuration_count_measurePreserving (μ : FiniteMeasure ℝ) :
    MeasurePreserving (fun ω : Configuration => ω.1) (configurationLaw μ) (poissonMeasure μ.mass) :=
  ⟨measurable_configuration_count, configurationLaw_count_map μ⟩

lemma configurationLaw_apply (μ : FiniteMeasure ℝ) {S : Set Configuration} (hS : MeasurableSet S) :
    configurationLaw μ S = ∑' N : ℕ, ENNReal.ofReal (poissonWeight μ.mass N) *
      arrayLaw μ N ((configurationMk N) ⁻¹' S) := by
  rw [configurationLaw, Measure.sum_apply _ hS]
  congr 1
  funext N
  rw [Measure.smul_apply, smul_eq_mul, fiberLaw, Measure.map_apply (measurable_configuration_mk N) hS]

lemma point_time_mark_independent (μ : FiniteMeasure ℝ) :
    IndepFun Prod.fst Prod.snd (pointLaw μ) :=
  indepFun_prod measurable_id measurable_id

lemma array_points_independent (μ : FiniteMeasure ℝ) (N : ℕ) :
    iIndepFun (fun (j : Fin N) (v : Fin N → Point) => v j) (arrayLaw μ N) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

noncomputable def worldLaw {Seed : Type*} [MeasurableSpace Seed] (μ : FiniteMeasure ℝ) (ν : Measure Seed) :
    Measure (World Seed) := (configurationLaw μ).prod ν

instance worldLaw_isProbability {Seed : Type*} [MeasurableSpace Seed]
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] : IsProbabilityMeasure (worldLaw μ ν) := by
  unfold worldLaw
  infer_instance

lemma configuration_seed_independent {Seed : Type*} [MeasurableSpace Seed]
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    IndepFun Prod.fst Prod.snd (worldLaw μ ν) :=
  indepFun_prod measurable_id measurable_id

lemma configuration_count_integrable (μ : FiniteMeasure ℝ) :
    Integrable (fun ω : Configuration => (ω.1 : ℝ)) (configurationLaw μ) :=
  (configuration_count_measurePreserving μ).integrable_comp_of_integrable (poisson_first_integrable μ.mass)

lemma configuration_count_expectation (μ : FiniteMeasure ℝ) :
    (∫ ω : Configuration, (ω.1 : ℝ) ∂configurationLaw μ) = (μ.mass : ℝ) := by
  have h := integral_map (μ := configurationLaw μ) measurable_configuration_count.aemeasurable
    (Measurable.of_discrete : Measurable (fun N : ℕ => (N : ℝ))).aestronglyMeasurable
  rw [configurationLaw_count_map μ, integral_poisson_first] at h
  exact h.symm

noncomputable def countingMeasure (ω : Configuration) : Measure Point :=
  ∑ j : Fin ω.1, Measure.dirac (ω.2 j)

lemma measurable_countingMeasure : Measurable countingMeasure := by
  apply measurable_of_configuration_branches
  intro N
  change Measurable (fun v : Fin N → Point => ∑ j : Fin N, Measure.dirac (v j))
  exact Finset.measurable_fun_sum _ (fun j _ => Measure.measurable_dirac.comp (measurable_pi_apply j))

lemma countingMeasure_univ (ω : Configuration) : countingMeasure ω univ = (ω.1 : ℝ≥0∞) := by
  simp [countingMeasure, Measure.coe_finsetSum, Finset.sum_apply]

/-- Every past anonymous point is recorded with its time and mark. No label or
future point count is present in this observation. -/
noncomputable def observedHistory (ω : Configuration) (t : ℝ) : Measure Point :=
  ∑ j : Fin ω.1, if (ω.2 j).1 < t then Measure.dirac (ω.2 j) else 0

lemma measurable_observedHistory (t : ℝ) : Measurable (fun ω => observedHistory ω t) := by
  apply measurable_of_configuration_branches
  intro N
  change Measurable (fun v : Fin N → Point => ∑ j : Fin N,
    if (v j).1 < t then Measure.dirac (v j) else 0)
  apply Finset.measurable_fun_sum
  intro j _
  exact Measurable.ite (measurableSet_lt (measurable_fst.comp (measurable_pi_apply j)) measurable_const)
    (Measure.measurable_dirac.comp (measurable_pi_apply j)) measurable_const

lemma observedHistory_snoc {N : ℕ} (v : Fin N → Point) (p : Point) (t : ℝ) :
    observedHistory ⟨N + 1, Fin.snoc v p⟩ t = observedHistory ⟨N, v⟩ t +
      (if p.1 < t then Measure.dirac p else 0) := by
  unfold observedHistory
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

lemma observedHistory_snoc_of_future {N : ℕ} (v : Fin N → Point) (p : Point) {t : ℝ} (hp : t ≤ p.1) :
    observedHistory ⟨N + 1, Fin.snoc v p⟩ t = observedHistory ⟨N, v⟩ t := by
  rw [observedHistory_snoc, if_neg (not_lt_of_ge hp), add_zero]

/-- A general anonymous history-dependent decision rule, common to all realized
Poisson counts. The independent auxiliary seed can encode arbitrary randomization. -/
structure AnonymousRule (Seed : Type*) where
  decide : Seed → ℝ → ℝ → Measure Point → Bool

def AnonymousRule.IsMeasurable {Seed : Type*} [MeasurableSpace Seed] (π : AnonymousRule Seed) : Prop :=
  Measurable (fun v : Seed × (Point × Measure Point) => π.decide v.1 v.2.1.1 v.2.1.2 v.2.2)

noncomputable def AnonymousRule.action {Seed : Type*} (π : AnonymousRule Seed) (r : Seed)
    {N : ℕ} (v : Fin N → Point) (j : Fin N) : Bool :=
  π.decide r (v j).1 (v j).2 (observedHistory ⟨N, v⟩ (v j).1)

/-- Adding an as-yet-unarrived point does not change an executed decision. The
actual total count is never an input to the strategy. -/
lemma AnonymousRule.action_snoc_of_future {Seed : Type*} (π : AnonymousRule Seed) (r : Seed)
    {N : ℕ} (v : Fin N → Point) (j : Fin N) (p : Point) (hp : (v j).1 ≤ p.1) :
    π.action r (Fin.snoc v p) j.castSucc = π.action r v j := by
  unfold AnonymousRule.action
  rw [Fin.snoc_castSucc, observedHistory_snoc_of_future v p hp]

lemma measurable_observedHistory_family {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (v : Ω → Fin N → Point) (hv : ∀ j, Measurable (fun ω => v ω j))
    (τ : Ω → ℝ) (hτ : Measurable τ) :
    Measurable (fun ω => observedHistory ⟨N, v ω⟩ (τ ω)) := by
  change Measurable (fun ω => ∑ j : Fin N,
    if (v ω j).1 < τ ω then Measure.dirac (v ω j) else 0)
  apply Finset.measurable_fun_sum
  intro j _
  exact Measurable.ite (measurableSet_lt (measurable_fst.comp (hv j)) hτ)
    (Measure.measurable_dirac.comp (hv j)) measurable_const

lemma AnonymousRule.measurable_action {Ω Seed : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]
    (π : AnonymousRule Seed) (hπ : π.IsMeasurable) {N : ℕ}
    (r : Ω → Seed) (hr : Measurable r) (v : Ω → Fin N → Point)
    (hv : ∀ j, Measurable (fun ω => v ω j)) (j : Fin N) :
    Measurable (fun ω => π.action (r ω) (v ω) j) := by
  have hh := measurable_observedHistory_family v hv (fun ω => (v ω j).1) (measurable_fst.comp (hv j))
  exact hπ.comp (hr.prodMk ((hv j).prodMk hh))

lemma observedHistory_permute {N : ℕ} (v : Fin N → Point) (e : Equiv.Perm (Fin N)) (t : ℝ) :
    observedHistory ⟨N, v ∘ e⟩ t = observedHistory ⟨N, v⟩ t := by
  unfold observedHistory
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Renaming generation labels preserves every anonymous decision. -/
lemma AnonymousRule.action_permute {Seed : Type*} (π : AnonymousRule Seed) (r : Seed)
    {N : ℕ} (v : Fin N → Point) (e : Equiv.Perm (Fin N)) (j : Fin N) :
    π.action r (v ∘ e) j = π.action r v (e j) := by
  unfold AnonymousRule.action
  simp only [Function.comp_apply]
  rw [observedHistory_permute]

end ProphetSecretary.Limiting
