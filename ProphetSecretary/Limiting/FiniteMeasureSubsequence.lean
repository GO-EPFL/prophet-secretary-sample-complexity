import ProphetSecretary.Limiting.BoundedMeasureCompactness

/-!
# Subsequences of bounded finite aggregate measures

A finite measure is its mass times its normalized probability law. Normalizing
a zero measure at the actual point zero preserves cap support, and continuity
of scalar multiplication transfers the independently extracted mass and law
limits back to genuine weak convergence of finite measures. No unproved
metrizability assumption on the finite-measure space is introduced.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

noncomputable def normalizeAtZero (μ : FiniteMeasure ℝ) : ProbabilityMeasure ℝ :=
  if μ = 0 then ⟨Measure.dirac 0,inferInstance⟩ else μ.normalize

lemma normalizeAtZero_supported_interval (μ : FiniteMeasure ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hcap : (μ : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    (normalizeAtZero μ : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 := by
  by_cases hzero : μ = 0
  · simp [normalizeAtZero,hzero,hH]
  · simp only [normalizeAtZero,if_neg hzero]
    rw [μ.toMeasure_normalize_eq_of_nonzero hzero,Measure.smul_apply,hcap]
    simp

lemma finiteMeasure_eq_mass_smul_normalizeAtZero (μ : FiniteMeasure ℝ) :
    μ = μ.mass • (normalizeAtZero μ).toFiniteMeasure := by
  by_cases hzero : μ = 0
  · simp [normalizeAtZero,hzero]
  · simpa only [normalizeAtZero,if_neg hzero] using μ.self_eq_mass_smul_normalize

/-- A cap and a mass bound supply an actual weakly convergent subsequence,
including sequences whose limiting total mass is zero. -/
theorem exists_finiteMeasure_weak_subsequence_supported_interval {H : ℝ} (hH : 0 ≤ H)
    (C : ℝ≥0) (measures : ℕ → FiniteMeasure ℝ)
    (hmass : ∀ m, (measures m).mass ≤ C)
    (hcap : ∀ m, (measures m : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    ∃ (μ : FiniteMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ μ.mass ≤ C ∧
      (μ : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 ∧ Tendsto (measures ∘ φ) atTop (𝓝 μ) := by
  let S : Set (ProbabilityMeasure ℝ) := {p | p (Icc (0 : ℝ) H)ᶜ = 0}
  let probs : ℕ → ProbabilityMeasure ℝ := fun m => normalizeAtZero (measures m)
  have hS : IsCompact S := isCompact_probabilityMeasures_supported_interval H
  have hprobs (m : ℕ) : probs m ∈ S :=
    (ProbabilityMeasure.null_iff_toMeasure_null _ _).mpr (normalizeAtZero_supported_interval _ hH (hcap m))
  obtain ⟨p,hp,φ,hφ,hprob⟩ := hS.isSeqCompact hprobs
  have hmassmem (m : ℕ) : (measures (φ m)).mass ∈ Icc (0 : ℝ≥0) C := ⟨by positivity,hmass _⟩
  obtain ⟨c,hc,ψ,hψ,hmassconv⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) C)).isSeqCompact hmassmem
  let μ : FiniteMeasure ℝ := c • p.toFiniteMeasure
  have hprob₂ : Tendsto (fun m => probs (φ (ψ m))) atTop (𝓝 p) := hprob.comp hψ.tendsto_atTop
  have hfinite : Tendsto (fun m => (probs (φ (ψ m))).toFiniteMeasure) atTop (𝓝 p.toFiniteMeasure) :=
    ((ProbabilityMeasure.toFiniteMeasure_isEmbedding ℝ).continuous.tendsto p).comp hprob₂
  have hconv := hmassconv.smul hfinite
  have heq : (fun m => (measures (φ (ψ m))).mass • (probs (φ (ψ m))).toFiniteMeasure) =
      fun m => measures (φ (ψ m)) := by
    funext m
    exact (finiteMeasure_eq_mass_smul_normalizeAtZero (measures (φ (ψ m)))).symm
  change Tendsto (fun m => (measures (φ (ψ m))).mass • (probs (φ (ψ m))).toFiniteMeasure) atTop (𝓝 μ) at hconv
  rw [heq] at hconv
  have hμmass : μ.mass = c := by
    change (c • p.toFiniteMeasure) Set.univ = c
    rw [FiniteMeasure.smul_apply,ProbabilityMeasure.toFiniteMeasure_apply_eq_apply]
    simp
  have hμcap : (μ : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 := by
    apply (FiniteMeasure.null_iff_toMeasure_null μ _).mp
    change (c • p.toFiniteMeasure) (Icc (0 : ℝ) H)ᶜ = 0
    rw [FiniteMeasure.smul_apply,ProbabilityMeasure.toFiniteMeasure_apply_eq_apply]
    have hp' : p (Icc (0 : ℝ) H)ᶜ = 0 := hp
    rw [hp']
    simp
  exact ⟨μ,φ ∘ ψ,hφ.comp hψ,hμmass ▸ hc.2,hμcap,hconv⟩

/-- One subsequence simultaneously controls every retained marginal and a
bounded finite aggregate measure. This asserts weak measure data only. -/
theorem exists_joint_marginal_aggregate_subsequence {H : ℝ} (hH : 0 ≤ H)
    (laws : ℕ → ℕ → ProbabilityMeasure ℝ)
    (hlaws : ∀ m i, (laws m i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0)
    (C : ℝ≥0) (measures : ℕ → FiniteMeasure ℝ) (hmass : ∀ m, (measures m).mass ≤ C)
    (hcap : ∀ m, (measures m : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    ∃ (Q : ℕ → ProbabilityMeasure ℝ) (μ : FiniteMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ (∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧ μ.mass ≤ C ∧
      (μ : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 ∧
      (∀ i, Tendsto (fun m => laws (φ m) i) atTop (𝓝 (Q i))) ∧
      Tendsto (measures ∘ φ) atTop (𝓝 μ) := by
  obtain ⟨Q,φ,hφ,hQ,hconv⟩ := exists_coordinatewise_weak_subsequence_supported_interval H laws hlaws
  obtain ⟨μ,ψ,hψ,hμmass,hμcap,hμconv⟩ := exists_finiteMeasure_weak_subsequence_supported_interval hH C
    (measures ∘ φ) (fun m => hmass (φ m)) (fun m => hcap (φ m))
  refine ⟨Q,μ,φ ∘ ψ,hφ.comp hψ,hQ,hμmass,hμcap,?_,hμconv⟩
  intro i
  exact (hconv i).comp hψ.tendsto_atTop

end ProphetSecretary.Limiting
