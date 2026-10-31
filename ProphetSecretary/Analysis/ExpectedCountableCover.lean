import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Averaging a nonnegative countable cover

Overlaps in a time-region cover only increase its upper bound. This lemma
passes such a cover to real expectations when the regional expectations are
summable, without assuming pointwise convergence of a policy sequence.
-/

open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace ProphetSecretary.Analysis

theorem integral_le_add_add_tsum_of_ofReal_cover {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F N G : Ω → ℝ} {E : ℕ → Ω → ℝ}
    (hFI : Integrable F μ) (hNI : Integrable N μ) (hGI : Integrable G μ)
    (hEI : ∀ j, Integrable (E j) μ)
    (hF0 : ∀ᵐ q ∂μ, 0 ≤ F q) (hN0 : ∀ᵐ q ∂μ, 0 ≤ N q)
    (hG0 : ∀ᵐ q ∂μ, 0 ≤ G q) (hE0 : ∀ j, ∀ᵐ q ∂μ, 0 ≤ E j q)
    (hsum : Summable (fun j => ∫ q, E j q ∂μ))
    (hcover : ∀ᵐ q ∂μ, ENNReal.ofReal (F q) ≤
      ENNReal.ofReal (N q) + ENNReal.ofReal (G q) + ∑' j, ENNReal.ofReal (E j q)) :
    (∫ q, F q ∂μ) ≤ (∫ q, N q ∂μ) + (∫ q, G q ∂μ) + ∑' j, ∫ q, E j q ∂μ := by
  have hEn j : 0 ≤ ∫ q, E j q ∂μ := integral_nonneg_of_ae (hE0 j)
  have hNn := integral_nonneg_of_ae hN0
  have hGn := integral_nonneg_of_ae hG0
  have hR : 0 ≤ (∫ q, N q ∂μ) + (∫ q, G q ∂μ) + ∑' j, ∫ q, E j q ∂μ :=
    add_nonneg (add_nonneg hNn hGn) (tsum_nonneg hEn)
  apply (ENNReal.ofReal_le_ofReal_iff hR).mp
  rw [ofReal_integral_eq_lintegral_ofReal hFI hF0]
  calc
    (∫⁻ q, ENNReal.ofReal (F q) ∂μ) ≤
        ∫⁻ q, ENNReal.ofReal (N q) + ENNReal.ofReal (G q) + ∑' j, ENNReal.ofReal (E j q) ∂μ :=
      lintegral_mono_ae hcover
    _ = ENNReal.ofReal ((∫ q, N q ∂μ) + (∫ q, G q ∂μ) + ∑' j, ∫ q, E j q ∂μ) := by
      have hNG : AEMeasurable (fun q => ENNReal.ofReal (N q) + ENNReal.ofReal (G q)) μ :=
        hNI.aemeasurable.ennreal_ofReal.add hGI.aemeasurable.ennreal_ofReal
      have hN : AEMeasurable (fun q => ENNReal.ofReal (N q)) μ := hNI.aemeasurable.ennreal_ofReal
      rw [lintegral_add_left' hNG,
        lintegral_add_left' hN,
        lintegral_tsum (fun j => (hEI j).aemeasurable.ennreal_ofReal)]
      simp_rw [← ofReal_integral_eq_lintegral_ofReal hNI hN0,
        ← ofReal_integral_eq_lintegral_ofReal hGI hG0]
      have heq : (∑' j, ∫⁻ q, ENNReal.ofReal (E j q) ∂μ) =
          ENNReal.ofReal (∑' j, ∫ q, E j q ∂μ) := by
        simp_rw [← ofReal_integral_eq_lintegral_ofReal (hEI _) (hE0 _)]
        exact (ENNReal.ofReal_tsum_of_nonneg hEn hsum).symm
      rw [heq, ENNReal.ofReal_add (add_nonneg hNn hGn) (tsum_nonneg hEn), ENNReal.ofReal_add hNn hGn]

end ProphetSecretary.Analysis
