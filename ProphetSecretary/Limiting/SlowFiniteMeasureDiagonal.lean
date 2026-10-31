import ProphetSecretary.Analysis.SlowDiagonal
import ProphetSecretary.Limiting.RareMarginal
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# A slow diagonal for countably many weak finite-measure limits

Adding one fixed atom makes normalization continuous even at zero original
mass. The augmented probability law and original mass form a metrizable
encoding. Subtracting the fixed atom in bounded continuous tests recovers
weak finite-measure convergence without assuming its metrizability.
-/
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology Classical NNReal
namespace ProphetSecretary.Limiting

lemma augmentZero_nonzero (μ : FiniteMeasure ℝ) : μ+diracZeroFiniteMeasure≠0 := by
  have hm : 0<(μ+diracZeroFiniteMeasure).mass := by
    simp only [FiniteMeasure.mass,FiniteMeasure.coeFn_add,Pi.add_apply,diracZeroFiniteMeasure_univ]
    positivity
  exact (FiniteMeasure.mass_nonzero_iff _).mp (ne_of_gt hm)

noncomputable def finiteMeasureDiagonalCode (μ : FiniteMeasure ℝ) : ProbabilityMeasure ℝ × ℝ :=
  ((μ+diracZeroFiniteMeasure).normalize,(μ.mass:ℝ))

lemma finiteMeasureDiagonalCode_tendsto {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun m => finiteMeasureDiagonalCode (μs m)) atTop (𝓝 (finiteMeasureDiagonalCode μ)) :=
  (FiniteMeasure.tendsto_normalize_of_tendsto (hμ.add_const diracZeroFiniteMeasure) (augmentZero_nonzero μ)).prodMk_nhds
    (NNReal.tendsto_coe.2 hμ.mass)

lemma finiteMeasure_tendsto_of_diagonalCode {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμ : Tendsto (fun m => finiteMeasureDiagonalCode (μs m)) atTop (𝓝 (finiteMeasureDiagonalCode μ))) :
    Tendsto μs atTop (𝓝 μ) := by
  have hNorm := (continuous_fst.tendsto _).comp hμ
  have hMass := NNReal.tendsto_coe.1 ((continuous_snd.tendsto _).comp hμ)
  have hAugMass : Tendsto (fun m => (μs m+diracZeroFiniteMeasure).mass) atTop
      (𝓝 (μ+diracZeroFiniteMeasure).mass) := by
    simpa only [FiniteMeasure.mass,FiniteMeasure.coeFn_add,Pi.add_apply,diracZeroFiniteMeasure_univ] using hMass.add_const 1
  have hAug := (FiniteMeasure.tendsto_normalize_iff_tendsto (augmentZero_nonzero μ)).mp ⟨hNorm,hAugMass⟩
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have h := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hAug f).sub_const (f 0)
  have he (κ : FiniteMeasure ℝ) :
      (∫ x, f x ∂((κ+diracZeroFiniteMeasure:FiniteMeasure ℝ):Measure ℝ))=(∫ x, f x ∂(κ:Measure ℝ))+f 0 := by
    rw [FiniteMeasure.toMeasure_add,integral_add_measure (f.integrable (κ:Measure ℝ)) (f.integrable (diracZeroFiniteMeasure:Measure ℝ))]
    congr 1
    simp only [diracZeroFiniteMeasure,FiniteMeasure.toMeasure_mk,integral_dirac]
  simpa only [he,add_sub_cancel_right] using h

/-- The original-sequence limit for each fixed prefix precedes the prefix
limit. The returned schedule preserves this order for every countable test. -/
theorem exists_slow_finiteMeasure_diagonal
    (A : ℕ → ℕ → ℕ → FiniteMeasure ℝ) (L : ℕ → ℕ → FiniteMeasure ℝ) (z : ℕ → FiniteMeasure ℝ)
    (hFirst : ∀ N j, Tendsto (fun m => A N m j) atTop (𝓝 (L N j)))
    (hSecond : ∀ j, Tendsto (fun N => L N j) atTop (𝓝 (z j))) :
    ∃ Ns : ℕ → ℕ, Monotone Ns ∧ (∀ m, Ns m≤m) ∧ Tendsto Ns atTop atTop ∧
      ∀ j, Tendsto (fun m => A (Ns m) m j) atTop (𝓝 (z j)) := by
  letI : PseudoMetricSpace (ProbabilityMeasure ℝ) := pseudoMetrizableSpacePseudoMetric _
  obtain ⟨Ns,hMono,hLe,hTop,hDiag⟩ := ProphetSecretary.Analysis.exists_slow_diagonal_of_iterated_limits
    (fun N m j => finiteMeasureDiagonalCode (A N m j))
    (fun N j => finiteMeasureDiagonalCode (L N j)) (fun j => finiteMeasureDiagonalCode (z j))
    (fun N j => finiteMeasureDiagonalCode_tendsto (hFirst N j))
    (fun j => finiteMeasureDiagonalCode_tendsto (hSecond j))
  exact ⟨Ns,hMono,hLe,hTop,fun j => finiteMeasure_tendsto_of_diagonalCode (hDiag j)⟩
end ProphetSecretary.Limiting
