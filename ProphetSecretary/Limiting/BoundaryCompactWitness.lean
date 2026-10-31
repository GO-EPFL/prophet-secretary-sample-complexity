import ProphetSecretary.Limiting.BoundaryCountersequence
import ProphetSecretary.Limiting.CompactExtraction
import ProphetSecretary.Limiting.NoReserve

/-!
# An actual critical compact witness from failure of boundary slack

Finite counterexamples are normalized before extraction. The common compact
limit therefore has M=1, reward-only value C_PS, and zero terminal reserve.
Every equality is obtained from actual value/benchmark convergence.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model

lemma exists_critical_countable_of_no_boundary_slack (H : ℝ≥0) (mu : ℝ) (hmu : 0<mu)
    (hFail : ∀ d : ℝ, 0<d → ∃ (n : ℕ) (P : Instance n),
      (∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ)) ∧ mu≤P.expectedMaximum ∧
      optimalScalarValue P 1 0-optimalCompetitiveRatio*P.expectedMaximum<d) :
    ∃ B : CountableInstance, B.cap=boundaryNormalizedCap H mu hmu ∧
      B.expectedMaximum=1 ∧ B.optimalScalarValue 1 0=optimalCompetitiveRatio ∧ B.terminal=0 := by
  obtain ⟨sizes,Q,hCap,hQM,hQV⟩ := exists_normalized_boundary_countersequence H mu hmu hFail
  obtain ⟨φ,hφ,B,wgt,hBCap,_hBands,hM,hV,_hUniform⟩ :=
    exists_cap_bounded_convergent_subsequence (boundaryNormalizedCap H mu hmu) sizes Q hCap
  have hMone : Tendsto (fun m => (Q (φ m)).expectedMaximum) atTop (𝓝 (1:ℝ)) := by
    simpa only [hQM] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 (1:ℝ)))
  have hMB : B.expectedMaximum=1 := tendsto_nhds_unique hM hMone
  have hVC := hQV.comp hφ.tendsto_atTop
  have hVB : B.optimalScalarValue 1 0=optimalCompetitiveRatio :=
    tendsto_nhds_unique (hV 1 0 zero_le_one le_rfl) hVC
  have hGap : B.scalarGap 1 0=0 := by
    simp only [CountableInstance.scalarGap,hMB,hVB,add_zero,mul_one,sub_self]
  exact ⟨B,hBCap,hMB,hVB,B.terminal_eq_zero_of_gap_nonpositive zero_lt_one le_rfl hGap.le⟩

end ProphetSecretary.Limiting
