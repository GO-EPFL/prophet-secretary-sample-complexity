import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The deterministic leave-one-out calibration inequality

For each observation omit that observation and calibrate the remaining sum.
Ordering the resulting roots bounds the sum of the held-out errors by one.
This is the finite inequality in the proof of `lem:duration-calibration`.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics

/-- Monotonicity and the omitted-sample root equations control the sum of
held-out errors, independently of the number of observations. -/
theorem calibration_leaveOneOut_sum_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : ℝ → ι → ℝ) (θ : ι → ℝ) {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hmono : ∀ i, Monotone (fun t => f t i))
    (hrange : ∀ i, f (θ i) i ∈ Set.Icc (0 : ℝ) 1)
    (hroot : ∀ i, ∑ j ∈ Finset.univ.erase i, (f (θ i) j - ρ) = 0) :
    |∑ i, (f (θ i) i - ρ)| ≤ 1 := by
  classical
  obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ θ Finset.univ_nonempty
  obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ θ Finset.univ_nonempty
  have root_sum (i : ι) : ∑ j, (f (θ i) j - ρ) = f (θ i) i - ρ := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hroot, zero_add]
  have hlow : f (θ lo) lo - ρ ≤ ∑ i, (f (θ i) i - ρ) := by
    rw [← root_sum lo]
    exact Finset.sum_le_sum fun i hi => sub_le_sub_right (hmono i (hlo i hi)) ρ
  have hupp : (∑ i, (f (θ i) i - ρ)) ≤ f (θ hi) hi - ρ := by
    rw [← root_sum hi]
    exact Finset.sum_le_sum fun i hi' => sub_le_sub_right (hmono i (hhi i hi')) ρ
  exact abs_le.mpr ⟨by linarith [(hrange lo).1, hρ.2],
    by linarith [(hrange hi).2, hρ.1]⟩

/-- The least root implements the tie convention for continuous calibration
curves. Its measurability and finite-piece implementation are separate properties. -/
noncomputable def durationCalibrationRoot (F : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  sInf {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ F t = ρ}

/-- Endpoint values ensure that the calibration equation has a least root. -/
theorem durationCalibrationRoot_isLeast (F : ℝ → ℝ) (hF : Continuous F)
    (h0 : F 0 = 0) (h1 : F 1 = 1) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    IsLeast {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ F t = ρ} (durationCalibrationRoot F ρ) := by
  have hc : IsCompact {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ F t = ρ} :=
    isCompact_Icc.inter_right (isClosed_eq hF continuous_const)
  have hn : ({t | t ∈ Set.Icc (0 : ℝ) 1 ∧ F t = ρ} : Set ℝ).Nonempty := by
    have hmem : ρ ∈ Set.Icc (F 0) (F 1) := by simpa [h0, h1] using hρ
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
      hF.continuousOn hmem
    exact ⟨t, ht, he⟩
  exact hc.isLeast_sInf hn

/-- For an ordered curve, passing a point is equivalent to passing its target. -/
theorem durationCalibrationRoot_le_iff (F : ℝ → ℝ) (hF : Continuous F)
    (hmono : Monotone F) (h0 : F 0 = 0) (h1 : F 1 = 1)
    {ρ t : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    durationCalibrationRoot F ρ ≤ t ↔ ρ ≤ F t := by
  have hr := durationCalibrationRoot_isLeast F hF h0 h1 hρ
  constructor
  · intro h
    rw [← hr.1.2]
    exact hmono h
  · intro h
    have hmem : ρ ∈ Set.Icc (F 0) (F t) := by simpa [h0] using And.intro hρ.1 h
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc ht.1 hF.continuousOn hmem
    exact (hr.2 (show s ∈ {q | q ∈ Set.Icc (0 : ℝ) 1 ∧ F q = ρ} from
      ⟨⟨hs.1, hs.2.trans ht.2⟩, he⟩)).trans hs.2

/-- Least-root selection is measurable when each evaluation of the random curve
and the target are measurable. This also covers independently selected targets. -/
theorem measurable_durationCalibrationRoot {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω → ℝ → ℝ) (ρ : Ω → ℝ)
    (hF : ∀ ω, Continuous (F ω)) (hmono : ∀ ω, Monotone (F ω))
    (h0 : ∀ ω, F ω 0 = 0) (h1 : ∀ ω, F ω 1 = 1)
    (hFm : ∀ t, Measurable (fun ω => F ω t)) (hρm : Measurable ρ)
    (hρ : ∀ ω, ρ ω ∈ Set.Icc (0 : ℝ) 1) :
    Measurable (fun ω => durationCalibrationRoot (F ω) (ρ ω)) := by
  apply measurable_of_Iic
  intro t
  by_cases ht0 : t < 0
  · have he : (fun ω => durationCalibrationRoot (F ω) (ρ ω)) ⁻¹' Set.Iic t = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      have hr := durationCalibrationRoot_isLeast (F ω) (hF ω) (h0 ω) (h1 ω) (hρ ω)
      exact not_le_of_gt (ht0.trans_le hr.1.1.1)
    rw [he]
    exact MeasurableSet.empty
  · by_cases ht1 : 1 ≤ t
    · have he : (fun ω => durationCalibrationRoot (F ω) (ρ ω)) ⁻¹' Set.Iic t = Set.univ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        have hr := durationCalibrationRoot_isLeast (F ω) (hF ω) (h0 ω) (h1 ω) (hρ ω)
        exact hr.1.1.2.trans ht1
      rw [he]
      exact MeasurableSet.univ
    · have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_not_gt ht0, le_of_not_ge ht1⟩
      have he : (fun ω => durationCalibrationRoot (F ω) (ρ ω)) ⁻¹' Set.Iic t =
          {ω | ρ ω ≤ F ω t} := by
        ext ω
        exact durationCalibrationRoot_le_iff (F ω) (hF ω) (hmono ω) (h0 ω) (h1 ω) (hρ ω) ht
      rw [he]
      exact measurableSet_le hρm (hFm t)

end ProphetSecretary.Statistics
