import ProphetSecretary.Limiting.UniformRareDesign
import ProphetSecretary.Model.WeakValueContinuity

/-!
# Weak convergence of a fixed finite rare design

Its virtual offer dimension is fixed before the original laws vary. No
normalized mark convergence or positive total intensity is needed.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma rareDesign_bounded (P : Model.Instance n) (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (k : ℕ) (hk : 0 < k) (hm : μ.mass ≤ (k : ℝ≥0)) :
    ∀ i, ∀ᵐ x ∂(rareDesign P μ H hμ k hk hm).law i, x ≤ (H : ℝ) := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [rareDesign,appendIID,Fin.addCases_left] using hP i
  | right j =>
    simpa only [rareDesign,appendIID,Fin.addCases_right] using
      (rareProbabilityLaw_bounds μ H hμ k (by exact_mod_cast hk) hm).mono (fun _ hx => hx.2)

lemma rareDesign_coordinatewise_weak {Γ : Type*} {l : Filter Γ}
    (Ps : Γ → Model.Instance n) (P : Model.Instance n) (μs : Γ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (H : ℝ≥0) (hs : ∀ m, ∀ᵐ x ∂(μs m : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (k : ℕ) (hk : 0 < k) (hms : ∀ m, (μs m).mass ≤ (k : ℝ≥0)) (hm : μ.mass ≤ (k : ℝ≥0))
    (hP : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) l (𝓝 (P.marginalProbabilityLaw i)))
    (hI : Tendsto μs l (𝓝 μ)) :
    ∀ i, Tendsto (fun m => (rareDesign (Ps m) (μs m) H (hs m) k hk (hms m)).marginalProbabilityLaw i) l
      (𝓝 ((rareDesign P μ H hμ k hk hm).marginalProbabilityLaw i)) := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [Model.Instance.marginalProbabilityLaw,rareDesign,appendIID,Fin.addCases_left] using hP i
  | right j =>
    convert rareProbabilityLaw_tendsto hI (k : ℝ≥0) (by exact_mod_cast hk) hms hm using 1
    · funext m
      apply Subtype.ext
      simp only [Model.Instance.marginalProbabilityLaw,rareDesign,appendIID,Fin.addCases_right]
      rfl
    · congr 1
      apply Subtype.ext
      simp only [Model.Instance.marginalProbabilityLaw,rareDesign,appendIID,Fin.addCases_right]
      rfl

lemma rareDesignError_mono_cap {H H' : ℝ≥0} (h : H ≤ H') (W R : ℝ≥0) (k : ℕ) :
    rareDesignError H W R k ≤ rareDesignError H' W R k := by
  unfold rareDesignError
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast h) W.property)
  positivity

/-- Every weakly converging sequence of finite intensities has an actual
common finite mass bound, including its finitely many initial elements. -/
lemma exists_uniform_mass_bound_of_tendsto (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ)) :
    ∃ R : ℝ≥0, μ.mass ≤ R ∧ ∀ m, (μs m).mass ≤ R := by
  have he : ∀ᶠ m in atTop, (μs m).mass < μ.mass+1 :=
    (tendsto_order.mp hweak.mass).2 (μ.mass+1) (by simp)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨μ.mass+1+∑ m ∈ Finset.range N, (μs m).mass,?_,?_⟩
  · exact (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (by positivity))
  · intro m
    by_cases hm : m < N
    · have hs : (μs m).mass ≤ ∑ j ∈ Finset.range N, (μs j).mass :=
        Finset.single_le_sum (f := fun j => (μs j).mass) (fun _ _ => by positivity) (Finset.mem_range.mpr hm)
      exact hs.trans (le_add_of_nonneg_left (by positivity))
    · exact (hN m (not_lt.mp hm)).le.trans (le_add_of_nonneg_right (by positivity))

end ProphetSecretary.Limiting
