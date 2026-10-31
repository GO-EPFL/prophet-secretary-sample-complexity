import ProphetSecretary.Model.Instance
import ProphetSecretary.Model.Training

/-!
# Independent training reservoirs

For a hard budget `k`, materializing `k` samples of each law before training gives the
same available fresh randomness as generating each requested sample when requested.
Only the entries supplied by the adaptive executor are observations. The online experiment
is independent of the whole reservoir and the auxiliary seed.
-/

open MeasureTheory ProbabilityTheory

namespace ProphetSecretary.Model
namespace Instance

variable {n : ℕ} (P : Instance n)

/-- Full independent training rounds: both indices refer to independent draws. -/
noncomputable def reservoirLaw (k : ℕ) : Measure (Reservoir n k) :=
  Measure.pi (fun i => Measure.pi (fun _ : Fin k => P.law i))

instance reservoirLaw_probability (k : ℕ) : IsProbabilityMeasure (P.reservoirLaw k) := by
  dsimp [reservoirLaw]
  infer_instance

/-- Training and any auxiliary randomness are drawn independently of the online instance.
The seed may contain correlated random choices for the training and online algorithms. -/
noncomputable def learningLaw (k : ℕ) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) := P.worldLaw ((P.reservoirLaw k).prod ν)

instance learningLaw_probability (k : ℕ) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] : IsProbabilityMeasure (P.learningLaw k ν) := by
  dsimp [learningLaw]
  infer_instance

/-- A training coordinate has exactly its stated marginal law. -/
theorem reservoir_coordinate_measurePreserving (k : ℕ) (i : Fin n) (j : Fin k) :
    MeasurePreserving (fun y : Reservoir n k => y i j) (P.reservoirLaw k) (P.law i) := by
  exact (measurePreserving_eval (fun _ : Fin k => P.law i) j).comp
    (measurePreserving_eval (fun i => Measure.pi (fun _ : Fin k => P.law i)) i)

/-- The reservoir and the auxiliary random seed are independent. -/
theorem reservoir_independent_seed (k : ℕ) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    IndepFun (fun z : Reservoir n k × Seed => z.1) (fun z => z.2)
      ((P.reservoirLaw k).prod ν) :=
  indepFun_prod measurable_id measurable_id

end Instance
end ProphetSecretary.Model
