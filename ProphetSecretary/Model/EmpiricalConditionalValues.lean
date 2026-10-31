import ProphetSecretary.Model.EmpiricalLearner
import ProphetSecretary.Model.EmpiricalMomentsMeasurability
import ProphetSecretary.Model.ScalarCoefficientMeasurability

/-!
# Conditional objectives after training

Training parameters are held fixed while integrating the independent online instance.
The resulting reward, duration, and scalar objective are jointly measurable functions
of the training array and auxiliary seed. The integrability statements are separate
from any empirical regret estimate.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Model

variable {n k : ℕ}

lemma Learner.measurable_frozenExpectedReward (L : Learner n k) (P : Instance n) :
    Measurable (fun p : Reservoir n k × L.Seed => (L.frozenRandomizedPolicy p.1 p.2).expectedReward P) := by
  let A := Reservoir n k × L.Seed
  let T := A × World n Unit
  have hx (i : Fin n) : Measurable (fun z : T => z.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hu (i : Fin n) : Measurable (fun z : T => z.2.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hf := L.policy.measurable_reward L.policy_isMeasurable
    (measurable_fst : Measurable fun z : T => z.1) hx hu Finset.univ
  have hm := (hf.stronglyMeasurable.integral_prod_right' (ν := P.worldLaw (Measure.dirac ()))).measurable
  convert hm using 1
  funext p
  rfl

lemma Learner.measurable_frozenExpectedDuration (L : Learner n k) (P : Instance n) :
    Measurable (fun p : Reservoir n k × L.Seed => (L.frozenRandomizedPolicy p.1 p.2).expectedDuration P) := by
  let A := Reservoir n k × L.Seed
  let T := A × World n Unit
  have hx (i : Fin n) : Measurable (fun z : T => z.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hu (i : Fin n) : Measurable (fun z : T => z.2.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hf := L.policy.measurable_stoppingTime L.policy_isMeasurable
    (measurable_fst : Measurable fun z : T => z.1) hx hu Finset.univ
  have hm := (hf.stronglyMeasurable.integral_prod_right' (ν := P.worldLaw (Measure.dirac ()))).measurable
  convert hm using 1
  funext p
  rfl

lemma Learner.measurable_frozenScalarObjective (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {W C : Reservoir n k × L.Seed → ℝ} (hW : Measurable W) (hC : Measurable C) :
    Measurable fun p => (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P (W p) (C p) := by
  have hm := (hW.mul (L.measurable_frozenExpectedReward P)).add
    (hC.mul (L.measurable_frozenExpectedDuration P))
  convert hm using 1
  funext p
  exact (L.frozenRandomizedPolicy p.1 p.2).scalarObjective_eq P hP (W p) (C p)

/-- A bounded nonnegative selected weight makes the conditional regret integrable.
This holds for every learner; no empirical optimality or statistical rate is assumed. -/
theorem Learner.integrable_selectedRegret (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {Z : Reservoir n k × L.Seed → ℝ} (hZ : Measurable Z)
    (hZ0 : ∀ p, 0 ≤ Z p) {zmax : ℝ}
    (hZmax : ∀ᵐ p ∂(P.reservoirLaw k).prod L.seedLaw, Z p ≤ zmax) :
    Integrable (fun p => optimalScalarValue P 1 (Z p) -
      (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p))
      ((P.reservoirLaw k).prod L.seedLaw) := by
  have hVmeas : Measurable (fun p : Reservoir n k × L.Seed => optimalScalarValue P 1 (Z p)) :=
    P.measurable_scalarValue_coefficients hP measurable_const hZ (fun _ => by norm_num) hZ0
  have hJmeas : Measurable (fun p : Reservoir n k × L.Seed => (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)) :=
    L.measurable_frozenScalarObjective P hP measurable_const hZ
  have hm := hVmeas.sub hJmeas
  apply Integrable.of_bound hm.aestronglyMeasurable (P.expectedMaximum + max 0 zmax)
  filter_upwards [hZmax] with p hp
  let π := L.frozenRandomizedPolicy p.1 p.2
  have hgap : 0 ≤ optimalScalarValue P 1 (Z p) - π.scalarObjective P 1 (Z p) :=
    sub_nonneg.mpr (scalarObjective_le_optimal π P hP (by norm_num) (hZ0 p))
  have hJ : 0 ≤ π.scalarObjective P 1 (Z p) := by
    rw [π.scalarObjective_eq P hP]
    exact add_nonneg (mul_nonneg zero_le_one (π.expectedReward_nonnegative P))
      (mul_nonneg (hZ0 p) (π.expectedDuration_nonnegative P))
  have hV := optimalScalarValue_le_benchmark P hP (by norm_num : (0 : ℝ) ≤ 1) (hZ0 p)
  rw [Real.norm_eq_abs]
  change |optimalScalarValue P 1 (Z p) - π.scalarObjective P 1 (Z p)| ≤ _
  rw [abs_of_nonneg hgap]
  have hmax := le_max_right (0 : ℝ) zmax
  nlinarith

end ProphetSecretary.Model
