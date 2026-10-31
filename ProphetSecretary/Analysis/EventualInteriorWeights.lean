import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Compact interior weights after finitely many indices

Convergence to an interior normalized weight permits one fixed compact
interval. Clamping changes only finitely many weights and preserves the
weight limit. This separates arbitrary initial endpoints from the asymptotic
score comparison.
-/
open Set Filter
open scoped Topology
namespace ProphetSecretary.Analysis

theorem exists_compact_interior_weight_sequence {lam : ℝ} (hlam : lam∈Ioo (0:ℝ) 1)
    (lams : ℕ → ℝ) (hLam : Tendsto lams atTop (𝓝 lam)) :
    ∃ δ : ℝ, 0<δ ∧ ∃ ls : ℕ → ℝ, (∀ m, ls m∈Icc δ (1-δ)) ∧
      ls=ᶠ[atTop] lams ∧ Tendsto ls atTop (𝓝 lam) := by
  let δ := min lam (1-lam)/2
  have hmin : 0<min lam (1-lam) := lt_min hlam.1 (sub_pos.mpr hlam.2)
  have hδ : 0<δ := half_pos hmin
  have hLeft : δ<lam := by
    have h := min_le_left lam (1-lam)
    dsimp [δ]
    linarith
  have hRight : lam<1-δ := by
    have h := min_le_right lam (1-lam)
    dsimp [δ]
    linarith
  have hOrder : δ≤1-δ := (hLeft.trans hRight).le
  let ls := fun m => max δ (min (1-δ) (lams m))
  have hRange (m) : ls m∈Icc δ (1-δ) := ⟨le_max_left _ _,max_le hOrder (min_le_left _ _)⟩
  have hEq : ls=ᶠ[atTop] lams := by
    filter_upwards [hLam.eventually (Ioo_mem_nhds hLeft hRight)] with m hm
    exact (max_eq_right (hm.1.le.trans_eq (min_eq_right hm.2.le).symm)).trans (min_eq_right hm.2.le)
  exact ⟨δ,hδ,ls,hRange,hEq,hLam.congr' hEq.symm⟩
end ProphetSecretary.Analysis
