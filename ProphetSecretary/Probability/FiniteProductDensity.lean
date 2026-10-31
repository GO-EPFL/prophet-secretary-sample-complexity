import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Densities in a finite independent product

Nonnegative integrable coordinate weights produce
the product density. Integrability includes almost-everywhere measurability.
The statement allows an arbitrary common marginal measurable space,
including the time/mark pairs in an actual finite Poisson configuration.
-/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace ProphetSecretary.Probability

lemma pi_withDensity_ofReal {ι : Type*} [Fintype ι] {A : Type*}
    [MeasurableSpace A] (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → A → ℝ) (hInt : ∀ i, Integrable (f i) (μ i))
    (hNonnegative : ∀ i, ∀ᵐ x ∂μ i, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x)))=
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  have hProductInt : Integrable (fun x => ∏ i, f i (x i)) (Measure.pi μ) :=
    Integrable.fintype_prod hInt
  have hProductNonnegative : ∀ᵐ x ∂Measure.pi μ, 0 ≤ ∏ i, f i (x i) := by
    have hEach : ∀ᵐ x ∂Measure.pi μ, ∀ i, 0 ≤ f i (x i) :=
      ae_all_iff.mpr (fun i => (measurePreserving_eval μ i).quasiMeasurePreserving.ae (hNonnegative i))
    exact hEach.mono (fun _ hx => Finset.prod_nonneg (fun i _ => hx i))
  apply Measure.pi_eq
  intro s hs
  have hRect := MeasurableSet.univ_pi hs
  have hFunction (x : ι → A) : (univ.pi s).indicator (fun x => ∏ i, f i (x i)) x=
      ∏ i, (s i).indicator (f i) (x i) := by
    by_cases hx : x ∈ univ.pi s
    · rw [indicator_of_mem hx]
      apply Finset.prod_congr rfl
      intro i _
      exact (indicator_of_mem (hx i (mem_univ i)) _).symm
    · have hNot : ∃ i, x i ∉ s i := by
        simpa only [mem_pi,mem_univ,forall_true_left,not_forall] using hx
      obtain ⟨i,hi⟩ := hNot
      rw [indicator_of_notMem hx]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)
  have hIndicatorNonnegative (i : ι) : 0 ≤ ∫ x, (s i).indicator (f i) x ∂μ i := by
    apply integral_nonneg_of_ae
    filter_upwards [hNonnegative i] with x hx
    change (0 : ℝ) ≤ (s i).indicator (f i) x
    by_cases hxs : x ∈ s i
    · simpa only [indicator_of_mem hxs] using hx
    · simpa only [indicator_of_notMem hxs,Pi.zero_apply] using (le_refl (0 : ℝ))
  rw [withDensity_apply _ hRect,
    ← ofReal_integral_eq_lintegral_ofReal hProductInt.integrableOn (ae_restrict_of_ae hProductNonnegative),
    ← integral_indicator hRect]
  simp_rw [hFunction]
  rw [integral_fintype_prod_eq_prod,ENNReal.ofReal_prod_of_nonneg (fun i _ => hIndicatorNonnegative i)]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i),
    ← ofReal_integral_eq_lintegral_ofReal (hInt i).integrableOn (ae_restrict_of_ae (hNonnegative i)),
    ← integral_indicator (hs i)]

end ProphetSecretary.Probability
