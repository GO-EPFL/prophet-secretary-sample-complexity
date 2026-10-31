import ProphetSecretary.Limiting.RareDesignBenchmark
import ProphetSecretary.Limiting.FiniteBandScalingReal

/-!
# Exact tail counts of the finite Poisson replacement

The virtual block contributes exactly the cutoff intensity tail. Bounded
intensity tilts preserve its tail bounds with one dimension-independent factor.
-/

open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

lemma rareDesign_tailCount_eq {n : ℕ} (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    (H : ℝ≥0) (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x∈Icc (0 : ℝ) H)
    (k : ℕ) (hk : 0<k) (hm : μ.mass≤(k : ℝ≥0)) {b : ℝ} (hb : 0≤b) :
    (rareDesign P μ H hμ k hk hm).tailCount b=P.tailCount b+(μ : Measure ℝ).real (Ioi b) := by
  unfold Model.Instance.tailCount
  rw [Fin.sum_univ_add]
  simp only [rareDesign,appendIID,Fin.addCases_left,Fin.addCases_right]
  change P.tailCount b+(∑ _ : Fin k,
    (rareProbabilityLaw μ (k : ℝ≥0) (by exact_mod_cast hk) hm : Measure ℝ).real (Ioi b))=
      P.tailCount b+(μ : Measure ℝ).real (Ioi b)
  simp only [rareProbabilityLaw_real_Ioi _ _ _ _ hb,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,NNReal.coe_natCast]
  rw [←mul_assoc,mul_inv_cancel₀ (ne_of_gt (Nat.cast_pos.mpr hk) : (k : ℝ)≠0),one_mul]

lemma bandScaledIntensity_real_le_quarter (μ : FiniteMeasure ℝ) {S A : Set ℝ}
    (hS : MeasurableSet S) (hA : MeasurableSet A) {θ : ℝ} (hθ : |θ|≤1/4)
    (r : ℝ≥0) (hr : (r : ℝ)=1+θ) :
    (bandScaledIntensity μ S r : Measure ℝ).real A≤(5/4)*(μ : Measure ℝ).real A := by
  rw [bandScaledIntensity_real_apply μ hS hA r,hr]
  have hUpper : θ≤1/4 := (abs_le.mp hθ).2
  have hIntersection : (μ : Measure ℝ).real (A∩S)≤(μ : Measure ℝ).real A :=
    measureReal_mono inter_subset_left
  have hTerm : θ*(μ : Measure ℝ).real (A∩S)≤(1/4)*(μ : Measure ℝ).real (A∩S) :=
    mul_le_mul_of_nonneg_right hUpper measureReal_nonneg
  nlinarith only [hTerm,hIntersection]

end ProphetSecretary.Limiting
