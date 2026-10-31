import ProphetSecretary.Model.Independence
import ProphetSecretary.Model.Measurability
import ProphetSecretary.Reach.Pathwise

/-!
# Laws of the pending execution

For `lem:monotone-reach` and `lem:strict-reach`, the pending execution is constructed
from the ordinary online decision rule by suppressing one identity. Its independence
from the suppressed value and arrival time follows from coordinate erasure.
-/

open MeasureTheory Set ProbabilityTheory

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

abbrev World (n : ℕ) (Seed : Type*) := (Fin n → ℝ) × ((Fin n → ℝ) × Seed)

lemma Policy.measurable_pendingWorldTime (π : Policy Seed n) (hπ : π.IsMeasurable)
    (i : Fin n) : Measurable (fun ω : World n Seed => π.pendingTime ω.2.2 ω.1 ω.2.1 i) := by
  exact π.measurable_stoppingTime hπ (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))
    (Finset.univ.erase i)

lemma Policy.measurable_worldTime (π : Policy Seed n) (hπ : π.IsMeasurable)
    (D : Finset (Fin n)) :
    Measurable (fun ω : World n Seed => π.stoppingTime ω.2.2 D ω.1 ω.2.1) := by
  exact π.measurable_stoppingTime hπ (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) D

namespace Instance

variable (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]

lemma world_clocks_measurePreserving :
    MeasurePreserving (fun ω : World n Seed => ω.2.1) (P.worldLaw ν) (clocksLaw n) := by
  exact (measurePreserving_fst (μ := clocksLaw n) (ν := ν)).comp
    (measurePreserving_snd (μ := P.valuesLaw) (ν := (clocksLaw n).prod ν))

lemma world_clock_measurePreserving (i : Fin n) :
    MeasurePreserving (fun ω : World n Seed => ω.2.1 i) (P.worldLaw ν) uniformClock := by
  exact (measurePreserving_eval (fun _ : Fin n => uniformClock) i).comp
    (P.world_clocks_measurePreserving ν)

lemma world_clock_map (i : Fin n) :
    (P.worldLaw ν).map (fun ω : World n Seed => ω.2.1 i) = uniformClock :=
  (P.world_clock_measurePreserving ν i).map_eq

lemma world_clocks_mem_unitInterval :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ i, ω.2.1 i ∈ Icc (0 : ℝ) 1 :=
  (P.world_clocks_measurePreserving ν).quasiMeasurePreserving.ae clocks_mem_unitInterval

lemma world_clocks_distinct :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, Function.Injective ω.2.1 :=
  (P.world_clocks_measurePreserving ν).quasiMeasurePreserving.ae clocks_pairwise_distinct

lemma pendingTime_candidate_independent (π : Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n) :
    IndepFun (fun ω : World n Seed => π.pendingTime ω.2.2 ω.1 ω.2.1 i)
      (fun ω => (ω.1 i, ω.2.1 i)) (P.worldLaw ν) := by
  apply P.erasedFunctional_candidate_independent ν i _ (π.measurable_pendingWorldTime hπ i)
  intro ω
  exact π.pendingTime_update ω.2.2 ω.1 ω.2.1 i 0 0

lemma pendingTime_clock_independent (π : Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n) :
    IndepFun (fun ω : World n Seed => π.pendingTime ω.2.2 ω.1 ω.2.1 i)
      (fun ω => ω.2.1 i) (P.worldLaw ν) :=
  (P.pendingTime_candidate_independent ν π hπ i).comp measurable_id measurable_snd

lemma pendingTime_value_independent (π : Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n) :
    IndepFun (fun ω : World n Seed => π.pendingTime ω.2.2 ω.1 ω.2.1 i)
      (fun ω => ω.1 i) (P.worldLaw ν) :=
  (P.pendingTime_candidate_independent ν π hπ i).comp measurable_id measurable_fst

lemma worldTime_mem_unitInterval (π : Policy Seed n) (D : Finset (Fin n)) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, π.stoppingTime ω.2.2 D ω.1 ω.2.1 ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hω
  exact ⟨π.stoppingTime_nonneg _ _ _ _ (fun j => (hω j).1), π.stoppingTime_le_one _ _ _ _⟩

lemma pendingTime_mem_unitInterval (π : Policy Seed n) (i : Fin n) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, π.pendingTime ω.2.2 ω.1 ω.2.1 i ∈ Icc (0 : ℝ) 1 :=
  P.worldTime_mem_unitInterval ν π (Finset.univ.erase i)

lemma integrable_worldTime (π : Policy Seed n) (hπ : π.IsMeasurable) (D : Finset (Fin n)) :
    Integrable (fun ω : World n Seed => π.stoppingTime ω.2.2 D ω.1 ω.2.1) (P.worldLaw ν) := by
  apply Integrable.of_bound (π.measurable_worldTime hπ D).aestronglyMeasurable 1
  filter_upwards [P.worldTime_mem_unitInterval ν π D] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2

lemma integrable_pendingTime (π : Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n) :
    Integrable (fun ω : World n Seed => π.pendingTime ω.2.2 ω.1 ω.2.1 i) (P.worldLaw ν) :=
  P.integrable_worldTime ν π hπ (Finset.univ.erase i)

end Instance
end ProphetSecretary.Model
