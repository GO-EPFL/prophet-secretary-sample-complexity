import ProphetSecretary.Statistics.FiniteGridPilotTail
import ProphetSecretary.Statistics.EmpiricalGapMoments
import ProphetSecretary.Probability.PilotMeanBound
import ProphetSecretary.Analysis.PilotTailIntegral

/-!
# Averaging the actual finite-grid pilot

This proves the first line of `eq:bayes-pilot` with an explicit integrated
sampling error. The empirical reference uses a fixed, deterministic weight.
The subsequent upward-bias estimate and comparison with the unrestricted
minimum gap are separate steps.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Analysis

variable {n k : ℕ} [NeZero k]

theorem finiteGridPilotWeight_mean_le_reference (P : Instance n) (G : Finset ℝ)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {lo hi δ : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ lo) (h1 : hi ≤ 1) (hlohi : lo ≤ hi)
    (hInterior : Icc lo hi ⊆ Icc δ (1-δ)) {a : ℝ} (ha : a∈Icc lo hi) :
    (∫ y, normalizedScalarGap P (finiteGridPilotWeight G lo hi h0 h1 hlohi y)
      ∂P.trainingCoordinateLaw k) ≤ normalizedScalarGap P a +
    2*(∫ y, normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a
      ∂P.trainingCoordinateLaw k) +
    2*((64*pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)+8*Real.pi)/(k : ℝ)) := by
  let L := finiteGridPilotWeight (n := n) (k := k) G lo hi h0 h1 hlohi
  let X := fun y => normalizedScalarGap P (L y)
  let Z := fun y : (Fin n × Fin k) → ℝ => normalizedScalarGap
    (totalEmpiricalInstance (reservoirCoordinates.symm y)) a
  let v := 64*pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)
  let q := fun s : ℝ => Real.exp (-((k : ℝ)*s/v))+min 1 (16/((k : ℝ)^2*s^2))
  have hP := P.integrable_maximum_of_bounded hcap
  have ha01 : a∈Ioc (0 : ℝ) 1 :=
    ⟨hδ.trans_le (hInterior ha).1,ha.2.trans h1⟩
  have hLRange (y : (Fin n × Fin k) → ℝ) : L y∈Icc (0 : ℝ) 1 :=
    Icc_subset_Icc h0 h1 (finiteGridPilotWeight_mem G lo hi h0 h1 hlohi y)
  have hXM : Measurable X := P.measurable_normalizedGap_of_weight hP
    (measurable_finiteGridPilotWeight G lo hi h0 h1 hlohi) hLRange
  have hXRange (y : (Fin n × Fin k) → ℝ) : X y∈Icc (0 : ℝ) 1 :=
    P.normalizedScalarGap_mem_unit hcap (hLRange y)
  have hXI : Integrable X (P.trainingCoordinateLaw k) := by
    apply Integrable.of_bound hXM.aestronglyMeasurable 1
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hXRange y).1]
      exact (hXRange y).2
  have hZI : Integrable Z (P.trainingCoordinateLaw k) := P.integrable_empiricalNormalizedGap hcap ha01
  have hZRange := P.empiricalNormalizedGap_mem_unit_ae (k := k) hcap ⟨ha01.1.le,ha01.2⟩
  have hv : 0 < v := by
    have hK := pilotFirstProjectionConstant_positive hδ
    have hS := P.totalFirstMoment_nonnegative
    dsimp only [v]
    positivity
  have hk : 0 < (k : ℝ) := by exact_mod_cast NeZero.pos k
  have hQI := fixed_weight_tail_integral hv hk
  have hq0 (s : ℝ) (_hs : s∈Ioi (0 : ℝ)) : 0 ≤ q s :=
    add_nonneg (Real.exp_pos _).le (le_min zero_le_one (by positivity))
  have hTail (s : ℝ) (hs : normalizedScalarGap P a ≤ s) :
      (P.trainingCoordinateLaw k).real {y | s < X y} ≤
      (P.trainingCoordinateLaw k).real {y | s/2 < Z y}+2*q s :=
    finiteGridPilotWeight_true_gap_tail P G hG hcap hδ h0 h1 hlohi hInterior ha hs
  have hMean := pilot_mean_le hXI hZI (Eventually.of_forall fun y => (hXRange y).1)
    (hZRange.mono fun _ h => h.1) (hZRange.mono fun _ h => h.2)
    (P.normalizedScalarGap_mem_unit hcap ⟨ha01.1.le,ha01.2⟩).1 hq0 hQI.1 hTail
  calc
    (∫ y, X y ∂P.trainingCoordinateLaw k) ≤ normalizedScalarGap P a+
        2*(∫ y, Z y ∂P.trainingCoordinateLaw k)+2*(∫ s in Ioi (0 : ℝ), q s) := hMean
    _ ≤ _ := by linarith only [hQI.2]

end ProphetSecretary.Statistics
