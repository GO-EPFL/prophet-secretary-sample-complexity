import ProphetSecretary.Limiting.CountablePendingWorld
import ProphetSecretary.Probability.InfiniteCoordinateReplacement
import ProphetSecretary.Model.ClockReplacement

/-!
# Fresh-clock replacement in the actual countable law

A fresh uniform candidate clock replaces its old coordinate while all values,
other clocks, the anonymous cloud and the independent seed are preserved.
The pushforward law is proved from infinite-product replacement and measurable
product regrouping.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

lemma individualWorld_clockReplacement_measurePreserving (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    MeasurePreserving (fun z : ((ℕ → ℝ) × ((ℕ → ℝ) × Seed)) × ℝ =>
      (z.1.1,(Function.update z.1.2.1 i z.2,z.1.2.2)))
      ((B.individualWorldLaw ν).prod Model.Instance.uniformClock) (B.individualWorldLaw ν) := by
  have h₀ := measurePreserving_prodAssoc B.individualValuesLaw
    (individualClocksLaw.prod ν) Model.Instance.uniformClock
  have h₁ := (MeasurePreserving.id B.individualValuesLaw).prod
    (Model.measurePreserving_swap_last individualClocksLaw ν Model.Instance.uniformClock)
  have h₂ := (MeasurePreserving.id B.individualValuesLaw).prod
    ((ProphetSecretary.Probability.infinite_replaceCoordinate_measurePreserving
      (fun _ : ℕ => Model.Instance.uniformClock) i).prod (MeasurePreserving.id ν))
  exact h₂.comp (h₁.comp h₀)

lemma replaceIndividualClock_measurePreserving (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    MeasurePreserving (replaceIndividualClock i)
      ((B.completeWorldLaw ν).prod Model.Instance.uniformClock) (B.completeWorldLaw ν) := by
  have h₀ := measurePreserving_prodAssoc B.bandConfigurationsLaw
    (B.individualWorldLaw ν) Model.Instance.uniformClock
  have h₁ := (MeasurePreserving.id B.bandConfigurationsLaw).prod
    (individualWorld_clockReplacement_measurePreserving B ν i)
  exact h₁.comp h₀

omit [MeasurableSpace Seed] in
lemma keepIndividualPending_replace_clock (i : ℕ) (z : CompleteWorld Seed × ℝ) :
    keepIndividualPending i (replaceIndividualClock i z)=keepIndividualPending i z.1 := by
  unfold keepIndividualPending pendingIndividualWorld replaceIndividualClock
  rw [Function.update_idem]

lemma individualClock_completeWorld_measurePreserving (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    MeasurePreserving (fun v : CompleteWorld Seed => v.2.2.1 i)
      (B.completeWorldLaw ν) Model.Instance.uniformClock :=
  (individualClock_measurePreserving i).comp
    (measurePreserving_fst.comp (measurePreserving_snd.comp measurePreserving_snd))

end ProphetSecretary.Limiting.CountableInstance
