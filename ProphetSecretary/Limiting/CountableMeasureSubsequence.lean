import ProphetSecretary.Limiting.FiniteMeasureSubsequence

/-!
# One weak subsequence for countably many bounded finite measures

Probability normalizations are extracted simultaneously, then all masses are
extracted on the countable product of compact mass intervals. Their actual
scalar products give the weak finite-measure limits. This supports consistent
retained-prefix residual data without assuming any extraction conclusions.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

theorem exists_countable_finiteMeasure_weak_subsequence {H : ℝ} (hH : 0 ≤ H) (C : ℕ → ℝ≥0)
    (measures : ℕ → ℕ → FiniteMeasure ℝ) (hmass : ∀ m i, (measures m i).mass ≤ C i)
    (hcap : ∀ m i, (measures m i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    ∃ (μ : ℕ → FiniteMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, (μ i).mass ≤ C i) ∧ (∀ i, (μ i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      ∀ i, Tendsto (fun m => measures (φ m) i) atTop (𝓝 (μ i)) := by
  let probs : ℕ → ℕ → ProbabilityMeasure ℝ := fun m i => normalizeAtZero (measures m i)
  have hpCap (m i : ℕ) : (probs m i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 :=
    normalizeAtZero_supported_interval _ hH (hcap m i)
  obtain ⟨p,φ,hφ,hp,hprob⟩ := exists_coordinatewise_weak_subsequence_supported_interval H probs hpCap
  let masses : ℕ → ℕ → ℝ≥0 := fun m i => (measures (φ m) i).mass
  have hMassCompact : IsCompact (Set.pi Set.univ (fun i : ℕ => Icc (0 : ℝ≥0) (C i))) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hMassMem (m : ℕ) : masses m ∈ Set.pi Set.univ (fun i : ℕ => Icc (0 : ℝ≥0) (C i)) := by
    intro i _
    exact ⟨by positivity,hmass _ _⟩
  obtain ⟨c,hc,ψ,hψ,hmassconv⟩ := hMassCompact.isSeqCompact hMassMem
  let μ : ℕ → FiniteMeasure ℝ := fun i => c i • (p i).toFiniteMeasure
  have hμmass (i : ℕ) : (μ i).mass = c i := by
    change (c i • (p i).toFiniteMeasure) Set.univ = c i
    rw [FiniteMeasure.smul_apply,ProbabilityMeasure.toFiniteMeasure_apply_eq_apply]
    simp
  have hμcap (i : ℕ) : (μ i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 := by
    apply (FiniteMeasure.null_iff_toMeasure_null (μ i) _).mp
    change (c i • (p i).toFiniteMeasure) (Icc (0 : ℝ) H)ᶜ = 0
    rw [FiniteMeasure.smul_apply,ProbabilityMeasure.toFiniteMeasure_apply_eq_apply]
    rw [(ProbabilityMeasure.null_iff_toMeasure_null _ _).mpr (hp i)]
    simp
  refine ⟨μ,φ ∘ ψ,hφ.comp hψ,(fun i => (hμmass i) ▸ (hc i (Set.mem_univ i)).2),hμcap,?_⟩
  intro i
  have hp₂ : Tendsto (fun m => probs (φ (ψ m)) i) atTop (𝓝 (p i)) := (hprob i).comp hψ.tendsto_atTop
  have hfinite := ((ProbabilityMeasure.toFiniteMeasure_isEmbedding ℝ).continuous.tendsto (p i)).comp hp₂
  have hmass₂ : Tendsto (fun m => (measures (φ (ψ m)) i).mass) atTop (𝓝 (c i)) :=
    ((continuous_apply i).tendsto c).comp hmassconv
  have hconv := hmass₂.smul hfinite
  have heq : (fun m => (measures (φ (ψ m)) i).mass • (probs (φ (ψ m)) i).toFiniteMeasure) =
      fun m => measures (φ (ψ m)) i := by
    funext m
    exact (finiteMeasure_eq_mass_smul_normalizeAtZero (measures (φ (ψ m)) i)).symm
  change Tendsto (fun m => (measures (φ (ψ m)) i).mass • (probs (φ (ψ m)) i).toFiniteMeasure) atTop (𝓝 (μ i)) at hconv
  rw [heq] at hconv
  exact hconv

/-- A single strict subsequence for every retained marginal and every
finite-prefix aggregate residual, before identifying any limiting process. -/
theorem exists_joint_countable_marginal_residual_subsequence {H : ℝ} (hH : 0 ≤ H)
    (laws : ℕ → ℕ → ProbabilityMeasure ℝ)
    (hlaws : ∀ m i, (laws m i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0)
    (C : ℕ → ℝ≥0) (measures : ℕ → ℕ → FiniteMeasure ℝ) (hmass : ∀ m i, (measures m i).mass ≤ C i)
    (hcap : ∀ m i, (measures m i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    ∃ (Q : ℕ → ProbabilityMeasure ℝ) (μ : ℕ → FiniteMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ (∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      (∀ i, (μ i).mass ≤ C i) ∧ (∀ i, (μ i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      (∀ i, Tendsto (fun m => laws (φ m) i) atTop (𝓝 (Q i))) ∧
      ∀ i, Tendsto (fun m => measures (φ m) i) atTop (𝓝 (μ i)) := by
  obtain ⟨Q,φ,hφ,hQ,hconv⟩ := exists_coordinatewise_weak_subsequence_supported_interval H laws hlaws
  obtain ⟨μ,ψ,hψ,hμmass,hμcap,hμconv⟩ := exists_countable_finiteMeasure_weak_subsequence hH C
    (fun m i => measures (φ m) i) (fun m i => hmass (φ m) i) (fun m i => hcap (φ m) i)
  refine ⟨Q,μ,φ ∘ ψ,hφ.comp hψ,hQ,hμmass,hμcap,?_,hμconv⟩
  intro i
  exact (hconv i).comp hψ.tendsto_atTop

end ProphetSecretary.Limiting
