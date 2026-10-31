import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Field.Basic

/-!
# The finite competitive ratio program

A mixed strategy p and a rate γ∈[0,1] are feasible when their expected payoff
at every nature action is at least γ times its benchmark. Nonnegative pure
payoffs make rate zero feasible. Compactness proves existence of a maximizer;
an explicit uniform deficit then bounds its rate from below.

This is the finite program `con:bounded-learner` / `eq:bayes-gamma-program`.
The statistical deficit is an input to this optimization lemma.
-/

open Set
open scoped Classical BigOperators

namespace ProphetSecretary.Analysis

variable {α Θ : Type*} [Fintype α]

def finiteRateFeasible (A : α → Θ → ℝ) (b : Θ → ℝ) : Set ((α → ℝ) × ℝ) :=
  {z | z.1∈stdSimplex ℝ α ∧ z.2∈Icc (0 : ℝ) 1 ∧ ∀ θ, z.2*b θ ≤ ∑ a, z.1 a*A a θ}

lemma isClosed_finiteRateFeasible (A : α → Θ → ℝ) (b : Θ → ℝ) : IsClosed (finiteRateFeasible A b) := by
  have hBase : IsClosed {z : (α → ℝ) × ℝ | z.1∈stdSimplex ℝ α ∧ z.2∈Icc (0 : ℝ) 1} :=
    (isClosed_stdSimplex ℝ α).prod isClosed_Icc
  have hConstraints : IsClosed {z : (α → ℝ) × ℝ | ∀ θ, z.2*b θ ≤ ∑ a, z.1 a*A a θ} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro θ
    apply isClosed_le
    · fun_prop
    · fun_prop
  simpa only [finiteRateFeasible,Set.setOf_and,inter_assoc] using hBase.inter hConstraints

lemma isCompact_finiteRateFeasible (A : α → Θ → ℝ) (b : Θ → ℝ) : IsCompact (finiteRateFeasible A b) :=
  ((isCompact_stdSimplex ℝ α).prod isCompact_Icc).of_isClosed_subset
    (isClosed_finiteRateFeasible A b) (fun _ hz => ⟨hz.1,hz.2.1⟩)

lemma finiteRateFeasible_nonempty [Nonempty α] (A : α → Θ → ℝ) (b : Θ → ℝ)
    (hA : ∀ a θ, 0 ≤ A a θ) : (finiteRateFeasible A b).Nonempty := by
  let a := Classical.arbitrary α
  refine ⟨(Pi.single a 1,0),single_mem_stdSimplex ℝ a,⟨le_rfl,zero_le_one⟩,?_⟩
  intro θ
  simpa only [zero_mul,Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hA a θ

lemma exists_finite_rate_maximizer [Nonempty α] (A : α → Θ → ℝ) (b : Θ → ℝ)
    (hA : ∀ a θ, 0 ≤ A a θ) :
    ∃ z∈finiteRateFeasible A b, ∀ w∈finiteRateFeasible A b, w.2 ≤ z.2 := by
  exact (isCompact_finiteRateFeasible A b).exists_isMaxOn (finiteRateFeasible_nonempty A b hA)
    continuous_snd.continuousOn

lemma feasible_rate_of_deficit (A : α → Θ → ℝ) (b : Θ → ℝ)
    (hA : ∀ a θ, 0 ≤ A a θ) (p : α → ℝ) (hp : p∈stdSimplex ℝ α)
    {C κ β : ℝ} (hC : C ≤ 1) (hκ : 0 ≤ κ) (hβ : 0 < β)
    (hBench : ∀ θ, β ≤ b θ) (hDeficit : ∀ θ, C*b θ-κ ≤ ∑ a, p a*A a θ) :
    (p,max 0 (C-κ/β))∈finiteRateFeasible A b := by
  have hRatio : 0 ≤ κ/β := div_nonneg hκ hβ.le
  refine ⟨hp,⟨le_max_left _ _,max_le zero_le_one (by linarith)⟩,?_⟩
  intro θ
  have hPay : 0 ≤ ∑ a, p a*A a θ := Finset.sum_nonneg (fun a _ => mul_nonneg (hp.1 a) (hA a θ))
  by_cases hLow : C-κ/β ≤ 0
  · simpa only [max_eq_left hLow,zero_mul] using hPay
  · rw [max_eq_right (le_of_not_ge hLow)]
    have hScale : κ ≤ (κ/β)*b θ := by
      calc
        κ = (κ/β)*β := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hBench θ) hRatio
    nlinarith only [hScale,hDeficit θ]

theorem exists_finite_rate_maximizer_ge [Nonempty α] (A : α → Θ → ℝ) (b : Θ → ℝ)
    (hA : ∀ a θ, 0 ≤ A a θ) (p : α → ℝ) (hp : p∈stdSimplex ℝ α)
    {C κ β : ℝ} (hC : C ≤ 1) (hκ : 0 ≤ κ) (hβ : 0 < β)
    (hBench : ∀ θ, β ≤ b θ) (hDeficit : ∀ θ, C*b θ-κ ≤ ∑ a, p a*A a θ) :
    ∃ z∈finiteRateFeasible A b, C-κ/β ≤ z.2 ∧ ∀ w∈finiteRateFeasible A b, w.2 ≤ z.2 := by
  obtain ⟨z,hz,hMax⟩ := exists_finite_rate_maximizer A b hA
  have hCandidate := feasible_rate_of_deficit A b hA p hp hC hκ hβ hBench hDeficit
  exact ⟨z,hz,(le_max_right _ _).trans (hMax _ hCandidate),hMax⟩

end ProphetSecretary.Analysis
