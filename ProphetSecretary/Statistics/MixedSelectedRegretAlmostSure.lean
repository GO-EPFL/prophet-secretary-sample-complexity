import ProphetSecretary.Statistics.MixedSelectedRegret

/-!
# Almost-sure selected-scalar range with known marginals

Measurable clipping changes the selector only on invalid null training outcomes.
Exact frozen canonical decisions transfer the objective on the valid event.
Integrability of the actual regret is explicit, and the learner's hard budget
continues to hold on every raw training/auxiliary outcome.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k] {Seed : Type} [MeasurableSpace Seed]

lemma Learner.mixedSelectedScalar_frozen_objective_congr (D : Instance n)
    (hD : Integrable Instance.maximum D.valuesLaw) (known : Finset (Fin n))
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    {Z Z' : Reservoir n k × Seed → ℝ} (hZ : Measurable Z) (hZ' : Measurable Z')
    (p : Reservoir n k × Seed) (he : Z p=Z' p) (hz : 0≤Z p) (P : Instance n) :
    ((Learner.mixedEmpiricalWithSelectedWeights D hD known Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p) =
    ((Learner.mixedEmpiricalWithSelectedWeights D hD known Seed ν (fun _ => 1) Z' measurable_const hZ').frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z' p) := by
  have hz' : 0≤Z' p := he ▸ hz
  rw [Learner.mixedEmpiricalWithSelectedWeights_frozen_objective_eq D hD known Seed ν (fun _ => 1) Z measurable_const hZ p.1 p.2 zero_lt_one hz,
    Learner.mixedEmpiricalWithSelectedWeights_frozen_objective_eq D hD known Seed ν (fun _ => 1) Z' measurable_const hZ' p.1 p.2 zero_lt_one hz']
  congr 1
  simp only [he]

theorem Learner.mixedSelectedScalar_expected_regret_integrable_bound_ae (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {Z : Reservoir n k × Seed → ℝ} {lo hi : ℝ}
    (hZ : Measurable Z) (hlo : 0<lo) (hlohi : lo≤hi)
    (hZrange : ∀ᵐ p ∂(P.reservoirLaw k).prod ν, Z p∈Icc lo hi) :
    let L := Learner.mixedEmpiricalWithSelectedWeights P (P.integrable_maximum_of_bounded hbound) known
      Seed ν (fun _ => 1) Z measurable_const hZ
    let F := fun p => optimalScalarValue P 1 (Z p)-(L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
    Integrable F ((P.reservoirLaw k).prod ν) ∧
      (∫ p, F p ∂(P.reservoirLaw k).prod ν) ≤
        empiricalCandidateRegretConstant lo hi*P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ) := by
  let Z' := fun p => max lo (min hi (Z p))
  have hm : Measurable Z' := measurable_const.max (measurable_const.min hZ)
  have hr (p) : Z' p∈Icc lo hi := ⟨le_max_left _ _,max_le hlohi (min_le_left _ _)⟩
  have he : Z =ᵐ[(P.reservoirLaw k).prod ν] Z' := hZrange.mono fun p hp => by
    dsimp [Z']
    rw [min_eq_right hp.2,max_eq_right hp.1]
  have hP := P.integrable_maximum_of_bounded hbound
  let L' := Learner.mixedEmpiricalWithSelectedWeights P hP known Seed ν (fun _ => 1) Z' measurable_const hm
  let F' := fun p => optimalScalarValue P 1 (Z' p)-(L'.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z' p)
  have hI : Integrable F' ((P.reservoirLaw k).prod ν) :=
    L'.integrable_selectedRegret P hP hm (fun p => (hlo.trans_le (hr p).1).le)
      (Eventually.of_forall fun p => (hr p).2)
  have hEq : (fun p => optimalScalarValue P 1 (Z p)-
      ((Learner.mixedEmpiricalWithSelectedWeights P hP known Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)) =ᵐ[(P.reservoirLaw k).prod ν] F' := by
    filter_upwards [he,hZrange] with p hp hz
    exact congrArg₂ (fun v j => v-j) (congrArg (optimalScalarValue P 1) hp)
      (Learner.mixedSelectedScalar_frozen_objective_congr P hP known ν hZ hm p hp (hlo.trans_le hz.1).le P)
  refine ⟨hI.congr hEq.symm,?_⟩
  rw [integral_congr_ae hEq]
  exact Learner.mixedSelectedScalar_expected_regret_le P known hbound ν hm hlo hlohi hr

/-- The selected-weight inequality needs only the paper's almost-sure range. -/
theorem Learner.mixedSelectedScalar_expected_regret_le_ae (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {Z : Reservoir n k × Seed → ℝ} {lo hi : ℝ}
    (hZ : Measurable Z) (hlo : 0<lo) (hlohi : lo≤hi)
    (hZrange : ∀ᵐ p ∂(P.reservoirLaw k).prod ν, Z p∈Icc lo hi) :
    (∫ p, optimalScalarValue P 1 (Z p)-
      ((Learner.mixedEmpiricalWithSelectedWeights P (P.integrable_maximum_of_bounded hbound) known
        Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
      ∂(P.reservoirLaw k).prod ν) ≤
      empiricalCandidateRegretConstant lo hi*P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ) :=
  (Learner.mixedSelectedScalar_expected_regret_integrable_bound_ae P known hbound ν hZ hlo hlohi hZrange).2

end ProphetSecretary.Model
