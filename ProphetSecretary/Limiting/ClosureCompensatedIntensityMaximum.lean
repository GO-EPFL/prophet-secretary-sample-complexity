import ProphetSecretary.Limiting.ClosureCompensatedIntensityFinite

/-!
# Largest band probability on the actual residual diagonal

The maximum is over existing labels only, with value zero for an empty residual.
Uniform residual rarity therefore gives a vanishing maximum without any
finite-support assumption on an offer distribution.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model

noncomputable def residualBandMaximum {n : ℕ} (P : Model.Instance n) (N : ℕ) (S : Set ℝ) : ℝ≥0 :=
  (Finset.univ.filter (fun j : Fin n => N≤j.val)).sup
    (fun j => ⟨(P.law j).real S,measureReal_nonneg⟩)

lemma residualBandMaximum_bounds {n : ℕ} (P : Model.Instance n) (N : ℕ) (S : Set ℝ)
    (j : Fin n) (hj : N≤j.val) : (P.law j).real S≤(residualBandMaximum P N S : ℝ) := by
  exact_mod_cast (Finset.le_sup (f := fun j : Fin n => (⟨(P.law j).real S,measureReal_nonneg⟩ : ℝ≥0))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩))

lemma residualBandMaximum_tendsto_zero {sizes : ℕ → ℕ} (P : ∀ m, Model.Instance (sizes m))
    (Ns : ℕ → ℕ) (S : Set ℝ)
    (hRare : ∀ ε>(0 : ℝ), ∀ᶠ m in atTop, ∀ j : Fin (sizes m), Ns m≤j.val → ((P m).law j).real S<ε) :
    Tendsto (fun m => (residualBandMaximum (P m) (Ns m) S : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hRare ε hε] with m hm
  have hp0 : (0 : ℝ)≤(residualBandMaximum (P m) (Ns m) S : ℝ) := (residualBandMaximum (P m) (Ns m) S).property
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hp0]
  change residualBandMaximum (P m) (Ns m) S<(⟨ε,hε.le⟩ : ℝ≥0)
  apply (Finset.sup_lt_iff (show (0 : ℝ≥0)<⟨ε,hε.le⟩ from hε)).mpr
  intro j hj
  exact hm j (Finset.mem_filter.mp hj).2

end ProphetSecretary.Limiting
