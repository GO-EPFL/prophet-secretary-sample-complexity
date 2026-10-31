import ProphetSecretary.Statistics.EmpiricalSelectedRate

/-!
# Almost-sure scalar-range formulation of `upstat:selected`

Measurable clipping changes the selector only on invalid null training outcomes.
The empirical learner remains defined with the same hard budget on every outcome.
Exact equality of frozen canonical decisions transfers the objective on the valid
event, so the statistical theorem needs only an almost-sure range assumption.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Seed : Type} [MeasurableSpace Seed]

lemma Learner.empiricalSelectedScalar_frozen_objective_congr
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    {Z Z' : Reservoir n k × Seed → ℝ} (hZ : Measurable Z) (hZ' : Measurable Z')
    (p : Reservoir n k × Seed) (he : Z p = Z' p) (hz : 0≤Z p) (P : Instance n) :
    ((Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p) =
    ((Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z' measurable_const hZ').frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z' p) := by
  have hz' : 0≤Z' p := he ▸ hz
  rw [Learner.empiricalWithSelectedWeights_frozen_objective_eq Seed ν (fun _ => 1) Z measurable_const hZ p.1 p.2 zero_lt_one hz,
    Learner.empiricalWithSelectedWeights_frozen_objective_eq Seed ν (fun _ => 1) Z' measurable_const hZ' p.1 p.2 zero_lt_one hz']
  congr 1
  simp only [he]

/-- The paper's measurable selected scalar may lie in its fixed positive
interval almost surely; no restriction is added on null training outcomes. -/
theorem Learner.empiricalSelectedScalar_expected_regret_le_ae (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {Z : Reservoir n k × Seed → ℝ} {lo hi : ℝ}
    (hZ : Measurable Z) (hlo : 0<lo) (hlohi : lo≤hi)
    (hZrange : ∀ᵐ p ∂(P.reservoirLaw k).prod ν, Z p∈Icc lo hi) :
    (∫ p, optimalScalarValue P 1 (Z p)-
      ((Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p) ∂(P.reservoirLaw k).prod ν) ≤
      empiricalCandidateRegretConstant lo hi * P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ) := by
  let Z' := fun p => max lo (min hi (Z p))
  have hm : Measurable Z' := measurable_const.max (measurable_const.min hZ)
  have hr (p) : Z' p∈Icc lo hi :=
    ⟨le_max_left _ _, max_le hlohi (min_le_left _ _)⟩
  have he : Z =ᵐ[(P.reservoirLaw k).prod ν] Z' := hZrange.mono fun p hp => by
    dsimp [Z']
    rw [min_eq_right hp.2,max_eq_right hp.1]
  have h := Learner.empiricalSelectedScalar_expected_regret_le P hbound ν hm hlo hlohi hr
  apply le_trans ?_ h
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [he,hZrange] with p hp hz
  exact congrArg₂ (fun v j => v-j) (congrArg (optimalScalarValue P 1) hp)
    (Learner.empiricalSelectedScalar_frozen_objective_congr ν hZ hm p hp (hlo.trans_le hz.1).le P)

end ProphetSecretary.Model
