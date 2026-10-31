import ProphetSecretary.Model.ArrivalRankTags
import ProphetSecretary.Probability.IIDPrefix

/-!
# Chronological finite tags from one independent infinite sequence

The auxiliary sequence is independent of all clocks before the random number
of arrivals is known. Its first N entries, assigned by chronological rank,
have exactly the independent product law jointly with those clocks.
-/

open MeasureTheory

namespace ProphetSecretary.Model.Instance

lemma arrivalRank_infiniteTags_measurePreserving {N : ℕ} {T : Type*} [MeasurableSpace T]
    (κ : Measure T) [IsProbabilityMeasure κ] :
    MeasurePreserving (fun z : (Fin N → ℝ) × (ℕ → T) => (z.1,fun i => z.2 (arrivalRank z.1 i).val))
      ((clocksLaw N).prod (Measure.infinitePi (fun _ : ℕ => κ)))
      ((clocksLaw N).prod (Measure.pi (fun _ : Fin N => κ))) :=
  (arrivalRank_tags_measurePreserving κ).comp
    ((MeasurePreserving.id (clocksLaw N)).prod (ProphetSecretary.Probability.iidPrefix_measurePreserving κ N))

end ProphetSecretary.Model.Instance
