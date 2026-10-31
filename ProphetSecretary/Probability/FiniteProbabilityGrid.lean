import ProphetSecretary.Probability.FiniteProbabilityRounding

/-!
# A finite grid of probability laws

A denominator-N law is encoded by bounded integer atom counts summing to N.
Every downward-rounded law belongs to this finite family, including its
compensating atom at zero. This is the probability grid in
`con:bounded-learner`.
-/

open Set
open scoped Classical BigOperators

namespace ProphetSecretary.Probability

variable (Θ : Type*) [Fintype Θ]

abbrev ProbabilityCounts (N : ℕ) := {a : Θ → Fin (N+1) // ∑ i, (a i : ℕ)=N}

variable {Θ}

noncomputable def countProbability {N : ℕ} (a : ProbabilityCounts Θ N) (i : Θ) : ℝ :=
  ((a.val i : ℕ) : ℝ)/(N : ℝ)

lemma countProbability_simplex {N : ℕ} (hN : 0<N) (a : ProbabilityCounts Θ N) :
    countProbability a∈stdSimplex ℝ Θ := by
  refine ⟨fun _ => by unfold countProbability; positivity, ?_⟩
  have hR : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  simp only [countProbability,← Finset.sum_div,← Nat.cast_sum,a.property,div_self hR]

lemma exists_probabilityCounts_of_grid {N : ℕ} (hN : 0<N) (p : Θ → ℝ)
    (hp : p∈stdSimplex ℝ Θ)
    (hGrid : ∀ i, ∃ j : ℕ, j≤N ∧ p i=(j : ℝ)/(N : ℝ)) :
    ∃ a : ProbabilityCounts Θ N, countProbability a=p := by
  classical
  choose j hjBound hjEq using hGrid
  let a : Θ → Fin (N+1) := fun i => ⟨j i,Nat.lt_succ_of_le (hjBound i)⟩
  have hSum : ∑ i, j i=N := by
    have hR : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
    have hs : (∑ i, ((j i : ℕ) : ℝ))/(N : ℝ)=1 := by
      rw [Finset.sum_div]
      simpa only [← hjEq] using hp.2
    have hs' := (div_eq_one_iff_eq hR).mp hs
    exact_mod_cast hs'
  refine ⟨⟨a,hSum⟩,?_⟩
  funext i
  exact (hjEq i).symm

lemma roundedProbability_mem_finite_grid [DecidableEq Θ] (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ)
    {N : ℕ} (hN : 0<N) (z : Θ) :
    ∃ a : ProbabilityCounts Θ N, countProbability a=roundedProbability p N z :=
  exists_probabilityCounts_of_grid hN _ (roundedProbability_simplex p hp hN z)
    (roundedProbability_integer_grid p hp hN z)

end ProphetSecretary.Probability
