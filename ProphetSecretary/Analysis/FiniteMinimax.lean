import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Finite minimax from Bayes responses

Sion's checked saddle-point theorem is applied to the two standard simplices.
All payoff functions are explicit finite sums. This is the finite-game step
in the paper; constructing the strategy alphabet and its statistical responses
is a separate application.
-/

open Set
open scoped BigOperators

namespace ProphetSecretary.Analysis

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

noncomputable def finiteWeightedLinear (c : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, c i*x i
  map_add' x y := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

noncomputable def finiteGamePayoff (u : α → β → ℝ) (p : β → ℝ) (q : α → ℝ) : ℝ :=
  ∑ b, (∑ a, u a b*q a)*p b

lemma finiteGamePayoff_right (u : α → β → ℝ) (p : β → ℝ) (q : α → ℝ) :
    finiteGamePayoff u p q = ∑ a, (∑ b, u a b*p b)*q a := by
  classical
  simp only [finiteGamePayoff,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma finiteGamePayoff_vertex [DecidableEq β] (u : α → β → ℝ) (b : β) (q : α → ℝ) :
    finiteGamePayoff u (Pi.single b 1) q = ∑ a, u a b*q a := by
  classical
  simp [finiteGamePayoff,Pi.single_apply]

/-- A response to every prior yields one mixture that works for every pure
nature action. The response condition is quantified before the universal mixture. -/
theorem finite_minimax_response [Nonempty α] (u : α → β → ℝ) (t : ℝ)
    (hResponse : ∀ p∈stdSimplex ℝ β, ∃ q∈stdSimplex ℝ α, t ≤ finiteGamePayoff u p q) :
    ∃ q∈stdSimplex ℝ α, ∀ b, t ≤ ∑ a, u a b*q a := by
  classical
  by_cases hβ : Nonempty β
  · letI := hβ
    have hX : (stdSimplex ℝ β).Nonempty := ⟨Pi.single (Classical.arbitrary β) 1,single_mem_stdSimplex ℝ _⟩
    have hY : (stdSimplex ℝ α).Nonempty := ⟨Pi.single (Classical.arbitrary α) 1,single_mem_stdSimplex ℝ _⟩
    have hLeft (q : α → ℝ) : QuasiconvexOn ℝ (stdSimplex ℝ β) (fun p => finiteGamePayoff u p q) :=
      (finiteWeightedLinear (fun b => ∑ a, u a b*q a)).convexOn (convex_stdSimplex ℝ β) |>.quasiconvexOn
    have hRight (p : β → ℝ) : QuasiconcaveOn ℝ (stdSimplex ℝ α) (fun q => finiteGamePayoff u p q) := by
      have h := (finiteWeightedLinear (fun a => ∑ b, u a b*p b)).concaveOn (convex_stdSimplex ℝ α) |>.quasiconcaveOn
      change QuasiconcaveOn ℝ (stdSimplex ℝ α) (fun q => ∑ a, (∑ b, u a b*p b)*q a) at h
      simpa only [← finiteGamePayoff_right] using h
    have hLower (q : α → ℝ) : LowerSemicontinuousOn (fun p => finiteGamePayoff u p q) (stdSimplex ℝ β) := by
      have h : Continuous (fun p => finiteGamePayoff u p q) := by unfold finiteGamePayoff; fun_prop
      exact h.continuousOn.lowerSemicontinuousOn
    have hUpper (p : β → ℝ) : UpperSemicontinuousOn (fun q => finiteGamePayoff u p q) (stdSimplex ℝ α) := by
      have h : Continuous (fun q => finiteGamePayoff u p q) := by unfold finiteGamePayoff; fun_prop
      exact h.continuousOn.upperSemicontinuousOn
    obtain ⟨p,hp,q,hq,hSaddle⟩ := Sion.exists_isSaddlePointOn (f := finiteGamePayoff u) hX (convex_stdSimplex ℝ β)
      (isCompact_stdSimplex ℝ β) (fun q _ => hLower q) (fun q _ => hLeft q)
      (convex_stdSimplex ℝ α) hY (isCompact_stdSimplex ℝ α)
      (fun p _ => hUpper p) (fun p _ => hRight p)
    obtain ⟨r,hr,hR⟩ := hResponse p hp
    refine ⟨q,hq,?_⟩
    intro b
    have h := hSaddle (Pi.single b 1) (single_mem_stdSimplex ℝ b) r hr
    rw [finiteGamePayoff_vertex] at h
    exact hR.trans h
  · haveI : IsEmpty β := not_nonempty_iff.mp hβ
    exact ⟨Pi.single (Classical.arbitrary α) 1,single_mem_stdSimplex ℝ _,fun b => isEmptyElim b⟩

end ProphetSecretary.Analysis
