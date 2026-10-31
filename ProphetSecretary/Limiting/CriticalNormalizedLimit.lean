import ProphetSecretary.Limiting.CriticalMinimizingSequence
import ProphetSecretary.Limiting.ScalarCriticalExtraction

/-!
# An actual normalized critical limiting instance

Cap-only compact extraction is applied to the constructed mean-one minimizing
sequence. Its actual maximum convergence fixes the limiting mean at one.
The result retains the original finite laws and their ordered body-convergence
witness, as well as compact-uniform scalar-value convergence. No bound on total
first moments is introduced. This supplies the critical-instance starting point
of `prop:critical-input`.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model

theorem exists_normalized_critical_ordered_limit :
    ∃ (B : CountableInstance) (a : ℝ), B.cap=3 ∧ B.terminal=0 ∧ B.expectedMaximum=1 ∧
      a∈Icc (1/4 : ℝ) (3/4) ∧ B.IsCritical a (1-a) ∧
      ∃ (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) (lam : ℕ → ℝ)
        (φ : ℕ → ℕ) (wgt : ℝ →ᵇ ℝ), StrictMono φ ∧
        (∀ m, (P m).expectedMaximum=1) ∧
        (∀ m i, ∀ᵐ x ∂(P m).law i, x≤3) ∧
        (∀ m, lam m∈Icc (1/4 : ℝ) (3/4)) ∧
        Tendsto (fun m => normalizedScalarGap (P m) (lam m)) atTop (𝓝 (0 : ℝ)) ∧
        OrderedBandConvergence (fun m => sizes (φ m)) (fun m => P (φ m)) wgt B ∧
        Tendsto (fun m => lam (φ m)) atTop (𝓝 a) ∧
        Tendsto (fun m => (P (φ m)).expectedMaximum) atTop (𝓝 B.expectedMaximum) ∧
        ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ z∈K, 0≤z.1 ∧ 0≤z.2) →
          TendstoUniformlyOn (fun m z => optimalScalarValue (P (φ m)) z.1 z.2)
            (fun z => B.optimalScalarValue z.1 z.2) atTop K := by
  obtain ⟨sizes,P,lam,_hP,hMean,hCap,hLam,_hGapBound,hGap⟩ := exists_normalized_nearCritical_sequence
  have hRange (m : ℕ) : lam m∈Icc (1/4 : ℝ) (1-1/4) := by
    simpa only [show (1 : ℝ)-1/4=3/4 by norm_num] using hLam m
  have hMeanLower (m : ℕ) : (1 : ℝ)≤(P m).expectedMaximum := by rw [hMean m]
  obtain ⟨φ,hφ,a,ha,B,wgt,hCapB,hBands,_hMB,hCritical,hZero,hLamLimit,hMaxLimit,hUniform⟩ :=
    exists_critical_ordered_subsequence 3 1 (1/4) (by norm_num) (by norm_num)
      sizes P hCap hMeanLower lam hRange hGap
  have hMeanConst : Tendsto (fun m => (P (φ m)).expectedMaximum) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hMean] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hMB : B.expectedMaximum=1 := tendsto_nhds_unique hMaxLimit hMeanConst
  have ha' : a∈Icc (1/4 : ℝ) (3/4) := by
    simpa only [show (1 : ℝ)-1/4=3/4 by norm_num] using ha
  exact ⟨B,a,hCapB,hZero,hMB,ha',hCritical,sizes,P,lam,φ,wgt,hφ,hMean,hCap,hLam,
    hGap,hBands,hLamLimit,hMaxLimit,hUniform⟩

end ProphetSecretary.Limiting
