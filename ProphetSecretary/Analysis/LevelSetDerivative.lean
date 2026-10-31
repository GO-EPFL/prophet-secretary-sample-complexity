import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Derivatives vanish almost everywhere on a level set

A point of a level set with nonzero derivative is isolated on its right within
that level set. Such points are countable in the real line. This treats atomic
endpoint equalities without assuming that the parameter level fibers are null.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Analysis

lemma countable_levelSet_nonzero_derivative (f : ℝ → ℝ) (c : ℝ) :
    {x : ℝ | f x = c ∧ deriv f x ≠ 0}.Countable := by
  let S := {x : ℝ | f x = c}
  apply (countable_setOf_isolated_right_within (s := S)).mono
  intro x hx
  refine ⟨hx.1, ?_⟩
  by_contra hn
  haveI : NeBot (𝓝[S ∩ Ioi x] x) := ⟨hn⟩
  have hsub : S ∩ Ioi x ⊆ ({x}ᶜ : Set ℝ) := by
    intro y hy
    simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_gt hy.2
  have hD := (differentiableAt_of_deriv_ne_zero hx.2).hasDerivAt.tendsto_slope.mono_left (nhdsWithin_mono x hsub)
  have h0 : Tendsto (slope f x) (𝓝[S ∩ Ioi x] x) (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyc : f y = c := hy.1
    rw [slope_def_field, hx.1, hyc, sub_self, zero_div]
  exact hx.2 (tendsto_nhds_unique hD h0)

/-- No regularity assumption on the function is needed: the total derivative is
zero by definition where differentiability fails. -/
lemma ae_derivative_zero_on_levelSet (f : ℝ → ℝ) (c : ℝ) :
    ∀ᵐ x : ℝ ∂volume, f x = c → deriv f x = 0 := by
  rw [ae_iff]
  have he : {x : ℝ | ¬ (f x = c → deriv f x = 0)} = {x : ℝ | f x = c ∧ deriv f x ≠ 0} := by
    ext x
    simp only [Classical.not_imp]
  rw [he]
  exact (countable_levelSet_nonzero_derivative f c).measure_zero volume

/-- Fubini permits an arbitrary measurable random level, including atomic
levels. Only the exceptional nonzero derivative is removed, not the level set. -/
lemma ae_derivative_zero_on_random_level {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (f : ℝ → ℝ) (hf : Measurable f)
    (L : Ω → ℝ) (hL : Measurable L) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂μ, f t = L ω → deriv f t = 0 := by
  have hEq : MeasurableSet {v : Ω × ℝ | f v.2 = L v.1} :=
    measurableSet_eq_fun (hf.comp measurable_snd) (hL.comp measurable_fst)
  have hD : MeasurableSet {v : Ω × ℝ | deriv f v.2 = 0} :=
    measurableSet_eq_fun ((measurable_deriv f).comp measurable_snd) measurable_const
  have hm : MeasurableSet {v : Ω × ℝ | f v.2 = L v.1 → deriv f v.2 = 0} := by
    have he : {v : Ω × ℝ | f v.2 = L v.1 → deriv f v.2 = 0} =
        {v : Ω × ℝ | f v.2 = L v.1}ᶜ ∪ {v : Ω × ℝ | deriv f v.2 = 0} := by
      ext v
      by_cases hv : f v.2 = L v.1 <;> simp [hv]
    rw [he]
    exact hEq.compl.union hD
  apply (Measure.ae_ae_comm hm).mp
  exact Filter.Eventually.of_forall (fun ω ↦ ae_derivative_zero_on_levelSet f (L ω))

/-- Local continuous parameter curves suffice: a measurable zero extension is
used only outside the open parameter interval, where no derivative is claimed. -/
lemma ae_derivative_zero_on_random_level_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (f : ℝ → ℝ) {a b : ℝ} (hf : ContinuousOn f (Ioo a b))
    (L : Ω → ℝ) (hL : Measurable L) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b), ∀ᵐ ω ∂μ, f t = L ω → deriv f t = 0 := by
  classical
  let F := (Ioo a b).piecewise f (fun _ ↦ (0 : ℝ))
  have hF : Measurable F := hf.measurable_piecewise continuousOn_const measurableSet_Ioo
  have hAE := ae_derivative_zero_on_random_level μ F hF L hL
  filter_upwards [ae_restrict_of_ae hAE, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  have hGerm : F =ᶠ[𝓝 t] f := by
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with q hq
    exact Set.piecewise_eq_of_mem (Ioo a b) f (fun _ ↦ (0 : ℝ)) hq
  have hValue : F t = f t := Set.piecewise_eq_of_mem (Ioo a b) f (fun _ ↦ (0 : ℝ)) hmem
  have hDeriv := hGerm.deriv_eq
  filter_upwards [ht] with ω hω
  intro hLevel
  have hz := hω (hValue.trans hLevel)
  rwa [hDeriv] at hz

end ProphetSecretary.Analysis
