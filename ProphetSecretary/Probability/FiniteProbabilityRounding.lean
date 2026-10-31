import ProphetSecretary.Probability.FiniteSimplexLaw
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Rounding finite probabilities downward and moving the loss to zero

The distinguished alphabet element represents a zero offer. Every other
probability is rounded down to a multiple of 1/N, and the missing mass goes
to the distinguished element. The total mass moved is explicitly bounded
by (alphabet size−1)/N.
-/

open Set
open scoped Classical BigOperators

namespace ProphetSecretary.Probability

variable {Θ : Type*} [Fintype Θ] [DecidableEq Θ]

noncomputable def floorProbability (N : ℕ) (p : ℝ) : ℝ := (⌊(N : ℝ)*p⌋₊ : ℝ)/(N : ℝ)

lemma floorProbability_nonnegative (N : ℕ) (p : ℝ) : 0 ≤ floorProbability N p := by
  unfold floorProbability
  positivity

lemma floorProbability_le {N : ℕ} (hN : 0 < N) {p : ℝ} (hp : 0 ≤ p) : floorProbability N p ≤ p := by
  have hR : 0 < (N : ℝ) := by exact_mod_cast hN
  unfold floorProbability
  apply (div_le_iff₀ hR).mpr
  simpa only [mul_comm] using Nat.floor_le (mul_nonneg hR.le hp)

lemma floorProbability_loss_lt {N : ℕ} (hN : 0 < N) (p : ℝ) : p-floorProbability N p < 1/(N : ℝ) := by
  have hR : 0 < (N : ℝ) := by exact_mod_cast hN
  have h := Nat.lt_floor_add_one ((N : ℝ)*p)
  unfold floorProbability
  apply (sub_lt_iff_lt_add).mpr
  rw [← add_div]
  apply (lt_div_iff₀ hR).mpr
  nlinarith only [h]

noncomputable def roundedProbability (p : Θ → ℝ) (N : ℕ) (z : Θ) (a : Θ) : ℝ :=
  if a=z then 1-∑ b∈Finset.univ.erase z, floorProbability N (p b) else floorProbability N (p a)

lemma roundedProbability_nonzero (p : Θ → ℝ) (N : ℕ) (z a : Θ) (ha : a≠z) :
    roundedProbability p N z a = floorProbability N (p a) := if_neg ha

lemma roundedProbability_zero (p : Θ → ℝ) (N : ℕ) (z : Θ) :
    roundedProbability p N z z = 1-∑ b∈Finset.univ.erase z, floorProbability N (p b) := if_pos rfl

lemma roundedProbability_simplex (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) {N : ℕ} (hN : 0 < N) (z : Θ) :
    roundedProbability p N z∈stdSimplex ℝ Θ := by
  have hSplit := Finset.sum_erase_add (s := Finset.univ) (f := p) (Finset.mem_univ z)
  rw [hp.2] at hSplit
  have hSum : (∑ b∈Finset.univ.erase z, floorProbability N (p b)) ≤ 1 := by
    calc
      _ ≤ ∑ b∈Finset.univ.erase z, p b := Finset.sum_le_sum (fun b _ => floorProbability_le hN (hp.1 b))
      _ ≤ 1 := by linarith only [hSplit,hp.1 z]
  refine ⟨fun a => ?_,?_⟩
  · by_cases ha : a=z
    · subst a
      rw [roundedProbability_zero]
      linarith only [hSum]
    · rw [roundedProbability_nonzero p N z a ha]
      exact floorProbability_nonnegative _ _
  · have h := Finset.sum_erase_add (s := Finset.univ) (f := roundedProbability p N z) (Finset.mem_univ z)
    have heq : (∑ b∈Finset.univ.erase z, roundedProbability p N z b) =
        ∑ b∈Finset.univ.erase z, floorProbability N (p b) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact roundedProbability_nonzero p N z b (Finset.mem_erase.mp hb).1
    rw [heq,roundedProbability_zero] at h
    linarith only [h]

noncomputable def roundingLoss (p : Θ → ℝ) (N : ℕ) (z : Θ) : ℝ :=
  ∑ a∈Finset.univ.erase z, (p a-floorProbability N (p a))

lemma roundingLoss_nonnegative (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) {N : ℕ} (hN : 0 < N) (z : Θ) :
    0 ≤ roundingLoss p N z := Finset.sum_nonneg (fun a _ => sub_nonneg.mpr (floorProbability_le hN (hp.1 a)))

lemma roundingLoss_le (p : Θ → ℝ) (N : ℕ) (hN : 0 < N) (z : Θ) :
    roundingLoss p N z ≤ ((Fintype.card Θ-1 : ℕ) : ℝ)/(N : ℝ) := by
  calc
    _ ≤ ∑ _a∈Finset.univ.erase z, (1/(N : ℝ)) :=
      Finset.sum_le_sum (fun a _ => (floorProbability_loss_lt hN (p a)).le)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_erase_of_mem (Finset.mem_univ z),Finset.card_univ]; ring

lemma roundedProbability_zero_loss (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) (N : ℕ) (z : Θ) :
    roundedProbability p N z z-p z = roundingLoss p N z := by
  have h := Finset.sum_erase_add (s := Finset.univ) (f := p) (Finset.mem_univ z)
  rw [hp.2] at h
  rw [roundedProbability_zero,roundingLoss,Finset.sum_sub_distrib]
  linarith only [h]

lemma roundedProbability_integer_grid (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) {N : ℕ} (hN : 0 < N)
    (z a : Θ) : ∃ j : ℕ, j≤N ∧ roundedProbability p N z a=(j : ℝ)/(N : ℝ) := by
  have hR : 0 < (N : ℝ) := by exact_mod_cast hN
  by_cases ha : a=z
  · subst a
    let K : ℕ := ∑ b∈Finset.univ.erase z, ⌊(N : ℝ)*p b⌋₊
    have hDiv : (K : ℝ)/(N : ℝ) = ∑ b∈Finset.univ.erase z, floorProbability N (p b) := by
      simp only [K,Nat.cast_sum,Finset.sum_div,floorProbability]
    have hSum : (K : ℝ)/(N : ℝ) ≤ 1 := by
      have h := (roundedProbability_simplex p hp hN z).1 z
      rw [roundedProbability_zero,← hDiv] at h
      linarith only [h]
    have hK : K≤N := by exact_mod_cast (div_le_one hR).mp hSum
    refine ⟨N-K,Nat.sub_le _ _,?_⟩
    rw [roundedProbability_zero,← hDiv,Nat.cast_sub hK]
    field_simp
  · refine ⟨⌊(N : ℝ)*p a⌋₊,?_,?_⟩
    · apply Nat.floor_le_of_le
      have h := (mem_Icc_of_mem_stdSimplex hp a).2
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h hR.le
    · rw [roundedProbability_nonzero p N z a ha]
      rfl

end ProphetSecretary.Probability
