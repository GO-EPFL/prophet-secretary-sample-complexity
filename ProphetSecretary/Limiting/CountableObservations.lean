import ProphetSecretary.Limiting.CountablePoissonBands
import ProphetSecretary.Limiting.ConfigurationMeasurability
import ProphetSecretary.Model.Measurability

/-!
# Observable histories of the countable configuration

All individual identities, including zero arrivals, are preserved. Anonymous
observations are a counting measure of past time/mark pairs: the band index,
array labels, and future counts are absent from this history.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

abbrev IndividualHistory := ℕ → Option Point

noncomputable def individualHistory (x u : ℕ → ℝ) (t : ℝ) : IndividualHistory :=
  fun i => if u i < t then some (u i,x i) else none

lemma measurable_individualHistory {Ω : Type*} [MeasurableSpace Ω]
    {x u : Ω → ℕ → ℝ} {t : Ω → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) (hu : ∀ i, Measurable (fun ω => u ω i))
    (ht : Measurable t) : Measurable (fun ω => individualHistory (x ω) (u ω) (t ω)) := by
  apply measurable_pi_lambda
  intro i
  have hh := Model.measurable_history (Finset.univ : Finset (Fin 1))
    (x := fun ω _ => x ω i) (u := fun ω _ => u ω i) (t := t)
    (fun _ => hx i) (fun _ => hu i) ht
  have he := (measurable_pi_apply (0 : Fin 1)).comp hh
  change Measurable (fun ω => Model.history (Finset.univ : Finset (Fin 1))
    (fun _ => x ω i) (fun _ => u ω i) (t ω) 0) at he
  simpa only [Model.history,Finset.mem_univ,true_and,individualHistory] using he

lemma measurable_observedHistory_joint :
    Measurable (fun q : Configuration × ℝ => observedHistory q.1 q.2) := by
  apply measurable_of_configuration_prod_branches
  intro N
  exact measurable_observedHistory_family (fun q : (Fin N → Point) × ℝ => q.1)
    (fun j => (measurable_pi_apply j).comp measurable_fst) Prod.snd measurable_snd

noncomputable def anonymousHistory (ω : BandConfigurations) (t : ℝ) : Measure Point :=
  Measure.sum (fun k => observedHistory (ω k) t)

lemma measurable_anonymousHistory {Ω : Type*} [MeasurableSpace Ω]
    {ω : Ω → BandConfigurations} {t : Ω → ℝ}
    (hω : Measurable ω) (ht : Measurable t) :
    Measurable (fun q => anonymousHistory (ω q) (t q)) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have he : (fun q => anonymousHistory (ω q) (t q) S) =
      fun q => ∑' k, observedHistory (ω q k) (t q) S := by
    funext q
    exact Measure.sum_apply _ hS
  rw [he]
  exact Measurable.tsum (fun k => (Measure.measurable_coe hS).comp
    (measurable_observedHistory_joint.comp (((measurable_pi_apply k).comp hω).prodMk ht)))

lemma individualHistory_zero_observed (x u : ℕ → ℝ) (t : ℝ) (i : ℕ)
    (hu : u i < t) (hx : x i = 0) : individualHistory x u t i = some (u i,0) := by
  simp only [individualHistory,if_pos hu,hx]

lemma individualHistory_before_arrival (x u : ℕ → ℝ) (t : ℝ) (i : ℕ)
    (hu : t ≤ u i) : individualHistory x u t i = none := by
  simp only [individualHistory,if_neg (not_lt_of_ge hu)]

variable (B : CountableInstance)

abbrev CompleteWorld (Seed : Type*) := BandConfigurations × ((ℕ → ℝ) × ((ℕ → ℝ) × Seed))

noncomputable def completeWorldLaw {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) :
    Measure (CompleteWorld Seed) := B.bandConfigurationsLaw.prod (B.individualWorldLaw ν)

instance completeWorldLaw_probability {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] : IsProbabilityMeasure (B.completeWorldLaw ν) := by
  unfold completeWorldLaw
  infer_instance

lemma configuration_individual_world_independent {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    IndepFun Prod.fst Prod.snd (B.completeWorldLaw ν) :=
  indepFun_prod measurable_id measurable_id

/-- General observable callbacks. This definition imposes no Markov or finite
support restriction. Admissibility requires a measurable first accepted point
whenever the callback accepts on the infinite configuration. -/
structure CountableRule (Seed : Type*) where
  individual : Seed → ℝ → ℕ → ℝ → IndividualHistory → Measure Point → Bool
  poisson : Seed → ℝ → ℝ → IndividualHistory → Measure Point → Bool

end ProphetSecretary.Limiting.CountableInstance
