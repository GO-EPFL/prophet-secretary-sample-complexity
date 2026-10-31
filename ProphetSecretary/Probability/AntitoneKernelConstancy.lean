import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Hull

/-!
# Pathwise constancy of an antitone kernel

A continuous conditional mean that is almost surely constant is constant on
the support. Bounded support supplies attained extreme points. The nonnegative
kernel difference at those two points has zero integral, so one conull event
makes the kernel constant throughout their interval. No uncountable union of
null sets is used.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Probability
variable {Ω : Type*} [MeasurableSpace Ω]

lemma bounded_probability_support_extrema (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (H : ℝ≥0) (hSupp : ∀ᵐ x ∂κ, x ∈ Icc (0 : ℝ) H) :
    ∃ a b : ℝ, IsLeast κ.support a ∧ IsGreatest κ.support b := by
  have hSub := κ.support_subset_of_isClosed isClosed_Icc hSupp
  have hCompact : IsCompact κ.support := isCompact_Icc.of_isClosed_subset κ.isClosed_support hSub
  have hNonempty := κ.nonempty_support (IsProbabilityMeasure.ne_zero κ)
  obtain ⟨a,ha⟩ := hCompact.exists_isLeast hNonempty
  obtain ⟨b,hb⟩ := hCompact.exists_isGreatest hNonempty
  exact ⟨a,b,ha,hb⟩

lemma convexHull_eq_Icc_of_extrema {S : Set ℝ} {a b : ℝ}
    (ha : IsLeast S a) (hb : IsGreatest S b) : convexHull ℝ S=Icc a b := by
  apply Set.Subset.antisymm
  · exact convexHull_min (fun x hx => ⟨ha.2 hx,hb.2 hx⟩) (convex_Icc a b)
  · have hSeg := (convex_convexHull ℝ S).segment_subset (subset_convexHull ℝ S ha.1) (subset_convexHull ℝ S hb.1)
    rwa [segment_eq_Icc (ha.2 hb.1)] at hSeg

theorem antitone_kernel_ae_constant_on_support_hull
    (μ : Measure Ω) (κ : Measure ℝ) [IsProbabilityMeasure κ] (H : ℝ≥0)
    (hSupp : ∀ᵐ x ∂κ, x ∈ Icc (0 : ℝ) H) (F : ℝ → Ω → ℝ)
    (hInt : ∀ x, Integrable (F x) μ) (hAnti : ∀ ω, Antitone (fun x => F x ω))
    (hCont : Continuous (fun x => ∫ ω, F x ω ∂μ))
    (hConstant : ∃ d : ℝ, (fun x => ∫ ω, F x ω ∂μ)=ᵐ[κ] fun _ => d) :
    ∃ a b : ℝ, IsLeast κ.support a ∧ IsGreatest κ.support b ∧
      ∀ᵐ ω ∂μ, ∀ x ∈ Icc a b, F x ω=F a ω := by
  obtain ⟨a,b,ha,hb⟩ := bounded_probability_support_extrema κ H hSupp
  obtain ⟨d,hd⟩ := hConstant
  have hOn : κ.support ⊆ {x : ℝ | (∫ ω, F x ω ∂μ)=d} :=
    κ.support_subset_of_isClosed (isClosed_eq hCont continuous_const) hd
  have hA : (∫ ω, F a ω ∂μ)=d := hOn ha.1
  have hB : (∫ ω, F b ω ∂μ)=d := hOn hb.1
  have hab : a ≤ b := ha.2 hb.1
  have hNonneg (ω : Ω) : 0 ≤ F a ω-F b ω := sub_nonneg.mpr (hAnti ω hab)
  have hZero : (∫ ω, F a ω-F b ω ∂μ)=0 := by rw [integral_sub (hInt a) (hInt b),hA,hB,sub_self]
  have hAE := (integral_eq_zero_iff_of_nonneg hNonneg ((hInt a).sub (hInt b))).mp hZero
  refine ⟨a,b,ha,hb,?_⟩
  filter_upwards [hAE] with ω hω x hx
  have hAB : F a ω=F b ω := sub_eq_zero.mp hω
  exact le_antisymm (hAnti ω hx.1) (hAB.le.trans (hAnti ω hx.2))

lemma mean_mem_Icc_of_support_extrema (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hInt : Integrable id κ) {a b : ℝ} (ha : IsLeast κ.support a) (hb : IsGreatest κ.support b) :
    (∫ x, x ∂κ) ∈ Icc a b := by
  have hSupport : ∀ᵐ x ∂κ, x ∈ κ.support := κ.support_mem_ae
  constructor
  · have h := integral_mono_ae (integrable_const a) hInt (hSupport.mono (fun x hx => ha.2 hx))
    simpa only [integral_const,probReal_univ,one_smul,id_eq] using h
  · have h := integral_mono_ae hInt (integrable_const b) (hSupport.mono (fun x hx => hb.2 hx))
    simpa only [integral_const,probReal_univ,one_smul,id_eq] using h

end ProphetSecretary.Probability
