import ProphetSecretary.Limiting.TailReserve
import Mathlib.Topology.Order.IsLUB

/-!
# Countably many bounded-tail bands above the extracted reserve

The reserve separator supplies actual finite uniform tail bounds on a strictly
decreasing sequence of levels tending to the reserve. These bounds precede
variable ordering and do not require a uniform first-moment bound.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

theorem exists_reserve_cutoffs_with_tail_bounds (a : ℝ) (L : ℕ → ℝ → ENNReal)
    (hbound : ∀ x, a < x → ∃ B : ENNReal, B < ⊤ ∧ ∀ m, L m x ≤ B) :
    ∃ (b : ℕ → ℝ) (B : ℕ → ℝ≥0), StrictAnti b ∧
      (∀ k, a < b k ∧ b k < a + 1) ∧ Tendsto b atTop (𝓝 a) ∧
      (∀ k, 1 ≤ B k) ∧ ∀ k m, L m (b k) ≤ (B k : ENNReal) := by
  obtain ⟨b,hanti,hmem,hlim⟩ := (dense_univ : Dense (Set.univ : Set ℝ)).exists_seq_strictAnti_tendsto_of_lt
    (show a < a+1 by linarith)
  have hb (k : ℕ) : a < b k ∧ b k < a+1 := (hmem k).1
  choose C hC hLC using fun k => hbound (b k) (hb k).1
  let B : ℕ → ℝ≥0 := fun k => (C k).toNNReal + 1
  refine ⟨b,B,hanti,hb,hlim,?_,?_⟩
  · intro k
    exact le_add_of_nonneg_left bot_le
  · intro k m
    exact (hLC k m).trans (by
      change C k ≤ ((C k).toNNReal : ENNReal) + 1
      rw [ENNReal.coe_toNNReal (hC k).ne]
      exact le_add_of_nonneg_right bot_le)

/-- All quantifiers are uniform in the original finite instance size. -/
theorem exists_finite_instance_reserve_cutoffs {H : ℝ} (hH : 0 ≤ H) (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m)) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ H) :
    ∃ (a : ℝ) (φ : ℕ → ℕ) (b : ℕ → ℝ) (B : ℕ → ℝ≥0),
      StrictMono φ ∧ a ∈ Icc (0 : ℝ) H ∧ StrictAnti b ∧
      (∀ k, a < b k ∧ b k < a+1) ∧ Tendsto b atTop (𝓝 a) ∧
      (∀ k, 1 ≤ B k) ∧ (∀ k m, extendedTailCount (P (φ m)) (b k) ≤ (B k : ENNReal)) ∧
      ∀ x, 0 ≤ x → x < a → Tendsto (fun m => extendedTailCount (P (φ m)) x) atTop (𝓝 ⊤) := by
  obtain ⟨a,φ,hφ,ha,hbelow,habove⟩ := exists_finite_instance_tail_separator hH sizes P hcap
  obtain ⟨b,B,hb,hba,hblim,hB,hbound⟩ := exists_reserve_cutoffs_with_tail_bounds a
    (fun m => extendedTailCount (P (φ m))) habove
  exact ⟨a,φ,b,B,hφ,ha,hb,hba,hblim,hB,hbound,hbelow⟩

end ProphetSecretary.Limiting
