import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

/-!
# Weak compactness of cap-supported marginal laws

Prokhorov's actual compactness theorem and the actual metrization of weak
convergence supply one subsequence for all countably many padded marginal
coordinates. This is a measure-data extraction step; it does not assert value,
policy, score or derivative convergence for limiting instances.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace ProphetSecretary.Limiting

/-- The cap-supported probability laws form a genuinely compact weak set. -/
theorem isCompact_probabilityMeasures_supported_interval (H : ℝ) :
    IsCompact {μ : ProbabilityMeasure ℝ | μ (Icc (0 : ℝ) H)ᶜ = 0} := by
  have h := isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
    (E := ℝ) (u := fun _ : ℕ => (0 : ℝ≥0)) (K := fun _ => Icc (0 : ℝ) H)
    tendsto_const_nhds (fun _ => isCompact_Icc) (Or.inl (inferInstance : NormalSpace ℝ))
  simpa using h

/-- A single countable diagonal extraction, with the subsequence chosen before
all retained indices. No coordinate-convergence conclusion is assumed. -/
theorem exists_coordinatewise_weak_subsequence_supported_interval (H : ℝ)
    (laws : ℕ → ℕ → ProbabilityMeasure ℝ)
    (hcap : ∀ m i, (laws m i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    ∃ (Q : ℕ → ProbabilityMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ (∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      ∀ i, Tendsto (fun m => laws (φ m) i) atTop (𝓝 (Q i)) := by
  let S : Set (ProbabilityMeasure ℝ) := {μ | μ (Icc (0 : ℝ) H)ᶜ = 0}
  have hS : IsCompact S := isCompact_probabilityMeasures_supported_interval H
  have hBig : IsCompact (Set.pi Set.univ (fun _ : ℕ => S)) := isCompact_univ_pi fun _ => hS
  have hmem (m : ℕ) : laws m ∈ Set.pi Set.univ (fun _ : ℕ => S) := by
    intro i _
    exact (ProbabilityMeasure.null_iff_toMeasure_null (laws m i) _).mpr (hcap m i)
  obtain ⟨Q,hQ,φ,hφ,hconv⟩ := hBig.isSeqCompact hmem
  refine ⟨Q,φ,hφ,?_,?_⟩
  · intro i
    exact (ProbabilityMeasure.null_iff_toMeasure_null (Q i) _).mp (hQ i (Set.mem_univ i))
  · intro i
    exact ((continuous_apply i).tendsto Q).comp hconv

end ProphetSecretary.Limiting
