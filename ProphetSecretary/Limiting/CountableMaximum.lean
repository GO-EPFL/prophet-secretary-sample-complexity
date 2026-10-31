import ProphetSecretary.Model.Instance
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Countable maxima as limits of finite maxima

A common finite cap makes the real supremum well defined almost surely. The
integral limit is proved on the actual probability space, not inferred from
convergence of stopping values.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Limiting

noncomputable def prefixMaximum (a : ℝ) (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  max a (Model.Instance.maximum (fun i : Fin N => f i.val))

noncomputable def countableMaximum (a : ℝ) (f : ℕ → ℝ) : ℝ :=
  ⨆ N, prefixMaximum a f N

lemma prefixMaximum_le {a H : ℝ} (ha : a ≤ H) (hH : 0 ≤ H)
    (f : ℕ → ℝ) (hf : ∀ i, f i ≤ H) (N : ℕ) : prefixMaximum a f N ≤ H :=
  max_le ha (Model.Instance.maximum_le _ hH (fun i => hf i.val))

lemma prefixMaximum_monotone (a : ℝ) (f : ℕ → ℝ) : Monotone (prefixMaximum a f) := by
  intro N M hNM
  apply max_le (le_max_left _ _)
  apply Model.Instance.maximum_le _ ((Model.Instance.maximum_nonnegative _).trans (le_max_right _ _))
  intro i
  exact (Model.Instance.le_maximum (fun j : Fin M => f j.val) ⟨i.val,lt_of_lt_of_le i.isLt hNM⟩).trans (le_max_right _ _)

lemma prefixMaximum_tendsto {a H : ℝ} (ha : a ≤ H) (hH : 0 ≤ H)
    (f : ℕ → ℝ) (hf : ∀ i, f i ≤ H) :
    Tendsto (prefixMaximum a f) atTop (𝓝 (countableMaximum a f)) :=
  tendsto_atTop_ciSup (prefixMaximum_monotone a f) ⟨H,fun _ ⟨N,hN⟩ => hN ▸ prefixMaximum_le ha hH f hf N⟩

lemma countableMaximum_le {a H : ℝ} (ha : a ≤ H) (hH : 0 ≤ H)
    (f : ℕ → ℝ) (hf : ∀ i, f i ≤ H) : countableMaximum a f ≤ H :=
  ciSup_le (fun N => prefixMaximum_le ha hH f hf N)

lemma le_countableMaximum {a H : ℝ} (ha : a ≤ H) (hH : 0 ≤ H)
    (f : ℕ → ℝ) (hf : ∀ i, f i ≤ H) (i : ℕ) : f i ≤ countableMaximum a f := by
  have hb : BddAbove (range (prefixMaximum a f)) := ⟨H,fun _ ⟨N,hN⟩ => hN ▸ prefixMaximum_le ha hH f hf N⟩
  exact ((Model.Instance.le_maximum (fun j : Fin (i+1) => f j.val) ⟨i,by omega⟩).trans
    (le_max_right _ _)).trans (le_ciSup hb (i+1))

lemma terminal_le_countableMaximum {a H : ℝ} (ha : a ≤ H) (hH : 0 ≤ H)
    (f : ℕ → ℝ) (hf : ∀ i, f i ≤ H) : a ≤ countableMaximum a f := by
  have hb : BddAbove (range (prefixMaximum a f)) := ⟨H,fun _ ⟨N,hN⟩ => hN ▸ prefixMaximum_le ha hH f hf N⟩
  exact (le_max_left _ _).trans (le_ciSup hb 0)

lemma measurable_prefixMaximum {Ω : Type*} [MeasurableSpace Ω] (a : ℝ)
    {f : Ω → ℕ → ℝ} (hf : ∀ i, Measurable (fun ω => f ω i)) (N : ℕ) :
    Measurable (fun ω => prefixMaximum a (f ω) N) :=
  measurable_const.max (Model.Instance.measurable_maximum.comp (measurable_pi_lambda _ (fun i => hf i.val)))

lemma measurable_countableMaximum {Ω : Type*} [MeasurableSpace Ω] (a : ℝ)
    {f : Ω → ℕ → ℝ} (hf : ∀ i, Measurable (fun ω => f ω i)) :
    Measurable (fun ω => countableMaximum a (f ω)) :=
  Measurable.iSup (fun N => measurable_prefixMaximum a hf N)

lemma integral_prefixMaximum_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {a H : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ H) (hH : 0 ≤ H)
    {f : Ω → ℕ → ℝ} (hf : ∀ i, Measurable (fun ω => f ω i))
    (hcap : ∀ᵐ ω ∂μ, ∀ i, f ω i ≤ H) :
    Tendsto (fun N => ∫ ω, prefixMaximum a (f ω) N ∂μ) atTop
      (𝓝 (∫ ω, countableMaximum a (f ω) ∂μ)) := by
  have hpInt (N : ℕ) : Integrable (fun ω => prefixMaximum a (f ω) N) μ := by
    apply Integrable.of_bound (measurable_prefixMaximum a hf N).aestronglyMeasurable H
    filter_upwards [hcap] with ω hω
    have hn : 0 ≤ prefixMaximum a (f ω) N := ha0.trans (le_max_left _ _)
    rw [Real.norm_eq_abs,abs_of_nonneg hn]
    exact prefixMaximum_le ha hH _ hω N
  have hInt : Integrable (fun ω => countableMaximum a (f ω)) μ := by
    apply Integrable.of_bound (measurable_countableMaximum a hf).aestronglyMeasurable H
    filter_upwards [hcap] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (ha0.trans (terminal_le_countableMaximum ha hH _ hω))]
    exact countableMaximum_le ha hH _ hω
  apply integral_tendsto_of_tendsto_of_monotone hpInt hInt
  · exact ae_of_all _ (fun _ => prefixMaximum_monotone a _)
  · exact hcap.mono (fun _ hω => prefixMaximum_tendsto ha hH _ hω)

end ProphetSecretary.Limiting
