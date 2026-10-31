import ProphetSecretary.Model.EmpiricalConditionalValues
import ProphetSecretary.Model.ScalarValueProperties

/-!
# Normalizing a data-selected scalar regret

For any actual learner, scaling both coefficients by 1/(1+z) preserves
the selected policy and decreases its nonnegative regret. The selected z
may depend on the whole training transcript and independent policy seed.
Integrability is proved before comparing the expectations.
-/

open MeasureTheory Set Filter
namespace ProphetSecretary.Model
variable {n k : ℕ}

theorem Learner.expected_normalized_regret_le_unnormalized (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (Z : Reservoir n k × L.Seed → ℝ) (hZ : Measurable Z) (hz : ∀ p, 0≤Z p) {zmax : ℝ}
    (hUpper : ∀ᵐ p ∂(P.reservoirLaw k).prod L.seedLaw, Z p≤zmax) :
    (∫ p, optimalScalarValue P (1/(1+Z p)) (Z p/(1+Z p))-
      (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P (1/(1+Z p)) (Z p/(1+Z p))
      ∂(P.reservoirLaw k).prod L.seedLaw) ≤
    ∫ p, optimalScalarValue P 1 (Z p)-(L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
      ∂(P.reservoirLaw k).prod L.seedLaw := by
  let D := (P.reservoirLaw k).prod L.seedLaw
  let gap := fun p : Reservoir n k × L.Seed => optimalScalarValue P 1 (Z p)-
    (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
  let W := fun p : Reservoir n k × L.Seed => 1/(1+Z p)
  have hW (p) : W p∈Icc (0 : ℝ) 1 := by
    refine ⟨one_div_nonneg.mpr (by linarith only [hz p]),?_⟩
    exact (one_div_le_one_div_of_le zero_lt_one (by linarith only [hz p])).trans_eq (by norm_num)
  have hMeas : Measurable W := measurable_const.div (measurable_const.add hZ)
  have hGap : Integrable gap D := L.integrable_selectedRegret P hP hZ hz hUpper
  have hWG : Integrable (fun p => W p*gap p) D := hGap.bdd_mul hMeas.aestronglyMeasurable
    (Eventually.of_forall (fun p => by rw [Real.norm_eq_abs,abs_of_nonneg (hW p).1]; exact (hW p).2))
  have hEq : (fun p : Reservoir n k × L.Seed => optimalScalarValue P (1/(1+Z p)) (Z p/(1+Z p))-
      (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P (1/(1+Z p)) (Z p/(1+Z p))) =
      (fun p => W p*gap p) := by
    funext p
    rw [optimalScalarValue_normalize P hP (hz p),RandomizedPolicy.scalarObjective_normalize _ P hP]
    dsimp only [W,gap]
    ring
  rw [hEq]
  apply integral_mono hWG hGap
  intro p
  have hNonneg : 0≤gap p := sub_nonneg.mpr
    (scalarObjective_le_optimal (L.frozenRandomizedPolicy p.1 p.2) P hP zero_le_one (hz p))
  exact mul_le_of_le_one_left hNonneg (hW p).2

end ProphetSecretary.Model
