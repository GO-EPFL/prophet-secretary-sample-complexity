import ProphetSecretary.Limiting.CompactBandExtraction
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Compact extraction of bounded instances

This is `lem:compact-extract`, with structural convergence at nonnegative tail
levels as in `def:body-convergence`: actual individual weak laws, residual
band limits in the stated order, rarity and the reserve tail dichotomy. One
subsequence also gives actual maximum convergence and full-policy scalar
convergence uniformly on every compact set of nonnegative weights.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting

/-- `lem:compact-extract`. The labels are the actual finite permutations
chosen by the ordering weight; padded laws outside each finite size are zero. -/
theorem exists_cap_bounded_convergent_subsequence (H : ℝ≥0) (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m)) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (B : CountableInstance) (wgt : ℝ →ᵇ ℝ), B.cap = H ∧
      OrderedBandConvergence (fun m => sizes (φ m)) (fun m => P (φ m)) wgt B ∧
      Tendsto (fun m => (P (φ m)).expectedMaximum) atTop (𝓝 B.expectedMaximum) ∧
      (∀ w c : ℝ, 0 ≤ w → 0 ≤ c →
        Tendsto (fun m => Model.optimalScalarValue (P (φ m)) w c) atTop (𝓝 (B.optimalScalarValue w c))) ∧
      ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ z ∈ K, 0 ≤ z.1 ∧ 0 ≤ z.2) →
        TendstoUniformlyOn (fun m z => Model.optimalScalarValue (P (φ m)) z.1 z.2)
          (fun z => B.optimalScalarValue z.1 z.2) atTop K := by
  obtain ⟨φ,hφ,B,wgt,hCap,hBands,hM,hRect⟩ := exists_cap_bounded_ordered_band_subsequence H sizes P hcap
  refine ⟨φ,hφ,B,wgt,hCap,hBands,hM,?_,?_⟩
  · intro w c hw hc
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hRect (⟨w,hw⟩ : ℝ≥0) (⟨c,hc⟩ : ℝ≥0) ε hε] with m hm
    simpa only [Real.dist_eq] using hm w c hw le_rfl hc le_rfl
  intro K hK hNonnegative
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨RW,hRW⟩ := (hK.image (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))).bddAbove
  obtain ⟨RC,hRC⟩ := (hK.image (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))).bddAbove
  let W : ℝ≥0 := ⟨max RW 0,le_max_right _ _⟩
  let C : ℝ≥0 := ⟨max RC 0,le_max_right _ _⟩
  filter_upwards [hRect W C ε hε] with m hm
  intro z hz
  have hw : z.1 ≤ (W : ℝ) := (hRW ⟨z,hz,rfl⟩).trans (le_max_left _ _)
  have hc : z.2 ≤ (C : ℝ) := (hRC ⟨z,hz,rfl⟩).trans (le_max_left _ _)
  rw [dist_comm,Real.dist_eq]
  exact hm z.1 z.2 (hNonnegative z hz).1 hw (hNonnegative z hz).2 hc

end ProphetSecretary.Limiting
