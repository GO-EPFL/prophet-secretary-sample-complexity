import ProphetSecretary.Limiting.ScheduledVirtualTail
import ProphetSecretary.Limiting.DirectVirtualScore
import ProphetSecretary.Limiting.CountableBandScore

/-!
# Actual scheduled zero-atom score components and their uniform information

The component array is indexed by the actual direct finite instance: retained
individuals receive zero and every virtual marginal uses zero-atom band
compensation. Its global bound and centering hold at every index. Information
on a fixed positive band is at most twice its limiting finite intensity.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Probability

noncomputable def directScheduledCloudScore (B : CountableInstance) (hZero : B.terminal=0) (S : Set ℝ) (m : ℕ) :
    Fin (m+B.directVirtualCount hZero m) → ℝ → ℝ :=
  directCloudScore m (B.directVirtualCount hZero m) (B.directVirtualOfferLaw hZero m:Measure ℝ) S

lemma directVirtualOfferLaw_zero_mass_ge_half (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    (1/2:ℝ)≤(B.directVirtualOfferLaw hZero m:Measure ℝ).real {0} := by
  rw [directVirtualOfferLaw,rareProbabilityLaw_eq_zeroInflated]
  apply directPoissonMarginal_zero_mass_ge_half
  rw [rareParameter_coe_eq_mass_div (B.directTruncation m).intensity (B.directVirtualCount hZero m)
    (B.directVirtualCount_positive hZero m) (B.directVirtualCount_rate_le hZero m)]
  exact B.directVirtualCount_probability_le_half hZero m

lemma directVirtualOfferLaw_positive_set_mass (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : (0:ℝ)∉S) :
    (B.directVirtualOfferLaw hZero m:Measure ℝ).real S=
      ((B.directTruncation m).intensity:Measure ℝ).real S/(B.directVirtualCount hZero m:ℝ) := by
  rw [directVirtualOfferLaw,rareProbabilityLaw_eq_zeroInflated]
  exact directPoissonMarginal_band_mass (B.directTruncation m).intensity
    (rareParameter (B.directTruncation m).intensity (B.directVirtualCount hZero m)
      (by exact_mod_cast B.directVirtualCount_positive hZero m) (B.directVirtualCount_rate_le hZero m))
    (B.directVirtualCount hZero m)
    (rareParameter_coe_eq_mass_div (B.directTruncation m).intensity (B.directVirtualCount hZero m)
      (B.directVirtualCount_positive hZero m) (B.directVirtualCount_rate_le hZero m)) hS hS0

theorem directScheduledCloudScore_properties (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : (0:ℝ)∉S) (m : ℕ) :
    (∀ j, Measurable (B.directScheduledCloudScore hZero S m j)) ∧
      (∀ j x, |B.directScheduledCloudScore hZero S m j x|≤1) ∧
      (∀ j, (∫ x, B.directScheduledCloudScore hZero S m j x ∂(B.directFiniteApproximation hZero m).law j)=0) ∧
      information (B.directFiniteApproximation hZero m).law (B.directScheduledCloudScore hZero S m)≤
        2*((B.directTruncation m).intensity:Measure ℝ).real S := by
  have h := directCloudScore_properties (B.individualPrefix m) (B.directVirtualOfferLaw hZero m:Measure ℝ)
    ((B.directVirtualOfferLaw_bounds hZero m).mono (fun _ hx => hx.1)) hS hS0
    (B.directVirtualOfferLaw_zero_mass_ge_half hZero m) (B.directVirtualCount_positive hZero m)
    (B.directVirtualOfferLaw_positive_set_mass hZero m hS hS0)
  refine ⟨h.1,h.2.1,?_,?_⟩
  · rw [B.directFiniteApproximation_eq_appendVirtual hZero m]
    exact h.2.2.1
  · rw [B.directFiniteApproximation_eq_appendVirtual hZero m]
    exact h.2.2.2

theorem directScheduledCloudScore_information_le (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b) (m : ℕ) :
    information (B.directFiniteApproximation hZero m).law (B.directScheduledCloudScore hZero S m)≤2*B.intensity.real S := by
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  have hENN : ((B.directTruncation m).intensity:Measure ℝ) S≤B.intensity S :=
    (Measure.restrict_le_self : B.intensity.restrict (Ioi (B.markCutoff m))≤B.intensity) S
  have hReal : ((B.directTruncation m).intensity:Measure ℝ).real S≤B.intensity.real S :=
    ENNReal.toReal_mono (B.intensity_band_finite hb hSub).ne hENN
  exact (B.directScheduledCloudScore_properties hZero hS hS0 m).2.2.2.trans
    (mul_le_mul_of_nonneg_left hReal (by norm_num))
end ProphetSecretary.Limiting.CountableInstance
