import ProphetSecretary.Limiting.HybridIndividualClock
import ProphetSecretary.Model.Restriction

/-!
# Uniform clock marginals of the actual hybrid execution

Any fixed subfamily of retained clocks remains an independent uniform product.
An additional integration time is independent of that subfamily. The explicit
measure-preserving projections justify applying clock hazard bounds even when
policies jointly depend on values, retained histories, and anonymous arrivals.
-/

open MeasureTheory

namespace ProphetSecretary.Limiting

variable {n m : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma hybridClocks_measurePreserving (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun v : HybridWorld n Seed => v.2.2.1)
      (hybridWorldLaw P μ ν) (Model.Instance.clocksLaw n) :=
  (P.world_clocks_measurePreserving ν).comp measurePreserving_snd

lemma hybridRestrictedClocks_measurePreserving (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (e : Fin m ↪ Fin n) :
    MeasurePreserving (fun v : HybridWorld n Seed => v.2.2.1 ∘ e)
      (hybridWorldLaw P μ ν) (Model.Instance.clocksLaw m) :=
  (Model.Instance.restrictClocks_measurePreserving e).comp (hybridClocks_measurePreserving P μ ν)

lemma hybridTimeRestrictedClocks_measurePreserving (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (e : Fin m ↪ Fin n) :
    MeasurePreserving (fun q : HybridWorld n Seed × ℝ => (q.2,q.1.2.2.1 ∘ e))
      ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock)
      (Model.Instance.uniformClock.prod (Model.Instance.clocksLaw m)) :=
  Measure.measurePreserving_swap.comp
    ((hybridRestrictedClocks_measurePreserving P μ ν e).prod (MeasurePreserving.id Model.Instance.uniformClock))

end ProphetSecretary.Limiting
