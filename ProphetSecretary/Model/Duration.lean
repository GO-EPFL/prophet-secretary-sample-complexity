import ProphetSecretary.Model.Outcome
import ProphetSecretary.Model.ScalarObjectives
import ProphetSecretary.Model.Bellman

/-!
# Positive duration in a finite instance

A finite execution cannot select before the first strictly positive arrival time.
The terminal convention gives duration one if it selects nothing, including on the
empty instance. This positivity is used in the clipping argument.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Instance.world_stoppingTime_positive (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (π : Policy Seed n) (D : Finset (Fin n)) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, 0 < π.stoppingTime ω.2.2 D ω.1 ω.2.1 := by
  filter_upwards [P.world_clocks_positive ν] with ω hω
  exact π.stoppingTime_positive _ _ _ _ hω

lemma RandomizedPolicy.expectedDuration_positive (π : RandomizedPolicy n) (P : Instance n) :
    0 < π.expectedDuration P := by
  let μ := P.worldLaw π.seedLaw
  have hp : ∀ᵐ ω : π.World ∂μ, 0 < π.realizedDuration ω :=
    P.world_stoppingTime_positive π.seedLaw π.rule Finset.univ
  have hs : Function.support π.realizedDuration =ᵐ[μ] (Set.univ : Set π.World) := by
    filter_upwards [hp] with ω hω
    apply propext
    constructor
    · intro _
      exact Set.mem_univ ω
    · intro _
      exact ne_of_gt hω
  have hm : μ (Function.support π.realizedDuration) = 1 := by
    rw [measure_congr hs]
    exact measure_univ
  apply (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h => h.le)
    (π.integrable_realizedDuration P)).mpr
  rw [hm]
  norm_num

end ProphetSecretary.Model
