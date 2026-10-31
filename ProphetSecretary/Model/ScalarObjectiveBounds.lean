import ProphetSecretary.Model.ScalarObjectives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Elementary bounds for scalar optimization

These results concern optimization within one finite instance. They do not assert the
paper's global reward--duration inequality, which requires the jackpot/zero argument.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model
namespace RandomizedPolicy

variable {n : ℕ}

/-- Always wait to the end. This policy works even for zero-mean auxiliary instances. -/
noncomputable def waiting (n : ℕ) : RandomizedPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := ⟨fun _ _ _ _ _ => false⟩
  measurable_rule := measurable_const

@[simp] lemma waiting_duration (ω : (waiting n).World) :
    (waiting n).realizedDuration ω = 1 := by
  simp [realizedDuration, waiting, Policy.stoppingTime, Policy.stopTimes,
    Policy.accepted, Policy.action]

@[simp] lemma waiting_reward (ω : (waiting n).World) :
    (waiting n).realizedReward ω = 0 := by
  simp [realizedReward, waiting, Policy.reward, Policy.ActualSelects, Policy.Selects,
    Policy.accepted, Policy.action]

@[simp] lemma waiting_scalarObjective (P : Instance n) (w c : ℝ) :
    (waiting n).scalarObjective P w c = c := by
  simp [scalarObjective]

lemma expectedDuration_nonnegative (π : RandomizedPolicy n) (P : Instance n) :
    0 ≤ π.expectedDuration P := by
  apply integral_nonneg_of_ae
  filter_upwards [P.worldTime_mem_unitInterval π.seedLaw π.rule Finset.univ] with ω hω
  exact hω.1

lemma expectedDuration_le_one (π : RandomizedPolicy n) (P : Instance n) :
    π.expectedDuration P ≤ 1 := by
  have h := integral_mono (π.integrable_realizedDuration P)
    (integrable_const (1 : ℝ)) (fun ω : π.World => π.rule.stoppingTime_le_one _ _ _ _)
  simpa [expectedDuration] using h

lemma scalarObjective_nonnegative (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    0 ≤ π.scalarObjective P w c := by
  rw [π.scalarObjective_eq P hP]
  exact add_nonneg (mul_nonneg hw (π.expectedReward_nonnegative P))
    (mul_nonneg hc (π.expectedDuration_nonnegative P))

lemma scalarObjective_le_benchmark (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    π.scalarObjective P w c ≤ w * P.expectedMaximum + c := by
  rw [π.scalarObjective_eq P hP]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (π.expectedReward_le_maximum P hP) hw
  · simpa using mul_le_mul_of_nonneg_left (π.expectedDuration_le_one P) hc

/-- Scaling the two coefficients scales a fixed policy's payoff, without reoptimization. -/
lemma scalarObjective_smul (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (a w c : ℝ) :
    π.scalarObjective P (a * w) (a * c) = a * π.scalarObjective P w c := by
  rw [π.scalarObjective_eq P hP, π.scalarObjective_eq P hP]
  ring

/-- Conversion of the fixed-policy objective `R+zτ` to normalized coefficients. -/
lemma scalarObjective_normalize (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (z : ℝ) :
    π.scalarObjective P (1 / (1 + z)) (z / (1 + z)) =
      (1 / (1 + z)) * π.scalarObjective P 1 z := by
  rw [π.scalarObjective_eq P hP, π.scalarObjective_eq P hP]
  ring

end RandomizedPolicy

variable {n : ℕ}

lemma scalarValues_nonempty (P : Instance n) (w c : ℝ) :
    {v | ∃ π : RandomizedPolicy n, v = π.scalarObjective P w c}.Nonempty :=
  ⟨_, ⟨RandomizedPolicy.waiting n, rfl⟩⟩

lemma scalarValues_bddAbove (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    BddAbove {v | ∃ π : RandomizedPolicy n, v = π.scalarObjective P w c} := by
  refine ⟨w * P.expectedMaximum + c, ?_⟩
  rintro v ⟨π, rfl⟩
  exact π.scalarObjective_le_benchmark P hP hw hc

lemma scalarObjective_le_optimal (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    π.scalarObjective P w c ≤ optimalScalarValue P w c :=
  le_csSup (scalarValues_bddAbove P hP hw hc) ⟨π, rfl⟩

lemma optimalScalarValue_le_benchmark (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue P w c ≤ w * P.expectedMaximum + c := by
  apply csSup_le (scalarValues_nonempty P w c)
  rintro v ⟨π, rfl⟩
  exact π.scalarObjective_le_benchmark P hP hw hc

lemma durationWeight_le_optimalScalarValue (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    c ≤ optimalScalarValue P w c := by
  simpa using scalarObjective_le_optimal (RandomizedPolicy.waiting n) P hP hw hc

lemma optimalScalarValue_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    0 ≤ optimalScalarValue P w c :=
  hc.trans (durationWeight_le_optimalScalarValue P hP hw hc)

end ProphetSecretary.Model
