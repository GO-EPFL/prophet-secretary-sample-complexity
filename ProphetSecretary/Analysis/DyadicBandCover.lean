import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.NormNum

/-!
# Coverage by the earlier dyadic value bands

Every value at least a>0 lies between 2^j a and 2^(j+1)a. Integrating over
this cover costs at most the sum of the band integrals. Overlaps at endpoints
are harmless, so no policy continuity or atomlessness is required here.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ProphetSecretary.Analysis

lemma exists_dyadic_band {a v : ℝ} (ha : 0 < a) (hv : a ≤ v) :
    ∃ j : ℕ, (2 : ℝ) ^ j * a ≤ v ∧ v ≤ (2 : ℝ) ^ (j + 1) * a := by
  have hr : 1 ≤ v / a := (le_div_iff₀ ha).mpr (by simpa only [one_mul] using hv)
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near hr (by norm_num : (1 : ℝ) < 2)
  exact ⟨j, (le_div_iff₀ ha).mp hj, ((div_lt_iff₀ ha).mp hj').le⟩

lemma ici_eq_iUnion_dyadic_bands {a : ℝ} (ha : 0 < a) :
    Ici a = ⋃ j : ℕ, Icc ((2 : ℝ) ^ j * a) ((2 : ℝ) ^ (j + 1) * a) := by
  ext v
  constructor
  · intro hv
    obtain ⟨j, hj, hj'⟩ := exists_dyadic_band ha hv
    exact mem_iUnion.mpr ⟨j, hj, hj'⟩
  · intro hv
    obtain ⟨j, hj⟩ := mem_iUnion.mp hv
    have hp : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hm := mul_le_mul_of_nonneg_right hp ha.le
    have hstart : a ≤ (2 : ℝ) ^ j * a := by simpa only [one_mul] using hm
    exact hstart.trans hj.1

/-- The nonnegative integral bound underlying the sum over earlier bands. -/
theorem lintegral_dyadic_band_cover_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (v : Ω → ℝ) (f : Ω → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    (∫⁻ ω in {ω | a ≤ v ω}, f ω ∂μ) ≤
      ∑' j : ℕ, ∫⁻ ω in {ω | (2 : ℝ) ^ j * a ≤ v ω ∧ v ω ≤ (2 : ℝ) ^ (j + 1) * a}, f ω ∂μ := by
  have hcover : {ω | a ≤ v ω} = ⋃ j : ℕ,
      {ω | (2 : ℝ) ^ j * a ≤ v ω ∧ v ω ≤ (2 : ℝ) ^ (j + 1) * a} := by
    ext ω
    simpa only [mem_setOf_eq, mem_Ici, mem_iUnion, mem_Icc] using
      (Set.ext_iff.mp (ici_eq_iUnion_dyadic_bands ha) (v ω))
  rw [hcover]
  exact lintegral_iUnion_le _ _

end ProphetSecretary.Analysis
