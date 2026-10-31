import ProphetSecretary.Analysis.TinyOfferElapsedIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Averaging a tiny-offer time loss

The only averaging premise is a deterministic-time mean estimate for M_t.
The actual empirical and true pending means satisfy it by separate proved
product-law identities. No conditioning on a selected scalar is used.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Analysis

theorem integral_averaged_tiny_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L : Ω × ℝ → ℝ} {M : ℝ → Ω → ℝ}
    (hI : Integrable L (μ.prod (volume.restrict (Icc (0 : ℝ) 1))))
    (hL0 : ∀ q t, 0 ≤ L (q,t)) {lo hi S x : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (hS : 0 ≤ S) (hx : 0 ≤ x)
    (hMI : ∀ t ∈ Icc (0 : ℝ) 1, Integrable (M t) μ)
    (hmean : ∀ t ∈ Icc (0 : ℝ) 1, (∫ q, M t q ∂μ) ≤ (1-t)*S)
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᵐ q ∂μ,
      L (q,t) ≤ (Icc (1 - x/lo) 1).indicator (fun t => x + M t q + hi*(1-t)) t) :
    (∫ q, (∫ t in Icc (0 : ℝ) 1, L (q,t)) ∂μ) ≤
      (1/lo + (2+hi)/lo^2)*(1+S)*x^2 := by
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  let G : ℝ → ℝ := fun t => ∫ q, L (q,t) ∂μ
  have hGI : Integrable G ν := hI.integral_prod_right
  have hG0 : ∀ᵐ t ∂ν, 0 ≤ G t := Eventually.of_forall fun t => integral_nonneg (fun q => hL0 q t)
  have hGD : ∀ᵐ t ∂ν, G t ≤
      (Icc (1-x/lo) 1).indicator (fun t => x+(2*S+hi)*(1-t)) t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hI.prod_left_ae] with t ht hLI
    have hM := hMI t ht
    by_cases hT : t ∈ Icc (1-x/lo) 1
    · rw [Set.indicator_of_mem hT]
      have hd : ∀ᵐ q ∂μ, L (q,t) ≤ x + M t q + hi*(1-t) := by
        simpa only [Set.indicator_of_mem hT] using hdom t ht
      have hR : Integrable (fun q => x + M t q + hi*(1-t)) μ :=
        ((integrable_const x).add hM).add (integrable_const _)
      have hv := integral_mono_ae hLI hR hd
      have heq : (∫ q, x + M t q + hi*(1-t) ∂μ) = x + (∫ q, M t q ∂μ) + hi*(1-t) := by
        rw [integral_add (f := fun q => x+M t q) (g := fun _ : Ω => hi*(1-t))
          ((integrable_const x).add hM) (integrable_const _),
          integral_add (f := fun _ : Ω => x) (g := M t) (integrable_const x) hM]
        simp only [integral_const, probReal_univ, one_smul]
      rw [heq] at hv
      have hμ := hmean t ht
      have hs := mul_nonneg hS (sub_nonneg.mpr ht.2)
      change G t ≤ _
      dsimp [G]
      linarith only [hv, hμ, hs]
    · rw [Set.indicator_of_notMem hT]
      apply integral_nonpos_of_ae
      change ∀ᵐ q ∂μ, L (q,t) ≤ (0 : ℝ)
      simpa only [Set.indicator_of_notMem hT] using hdom t ht
  have hb := tiny_offer_elapsed_integral_le hlo hhi hS hx hGI.aestronglyMeasurable hG0 hGD
  have heq : (∫ q, (∫ t in Icc (0 : ℝ) 1, L (q,t)) ∂μ) = ∫ t, G t ∂ν :=
    (integral_prod L hI).symm.trans (integral_prod_symm L hI)
  exact heq.le.trans hb

end ProphetSecretary.Analysis
