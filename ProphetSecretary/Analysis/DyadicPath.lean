import ProphetSecretary.Reach.Dyadic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Continuous processes and dyadic endpoint suprema
The dyadic maximum retains both endpoints. Continuity on the closed interval
identifies its countable supremum with the full interval supremum.
-/
open Set Filter
open scoped BigOperators Topology Classical
namespace ProphetSecretary.Analysis
open ProphetSecretary.Reach.EmpiricalChaining
variable {Ω : Type*}

def liftProcess (f : Ω → ℝ → ℝ) (ω : Ω) (t : ℝ) : ℝ := t + f ω t

lemma lifted_gridDeviation (f : Ω → ℝ → ℝ) (j k : ℕ) (ω : Ω) :
    gridDeviation (liftProcess f) j k ω = f ω (gridPoint j k) := by
  unfold gridDeviation liftProcess
  ring

lemma gridPoint_mem_unitInterval (j : ℕ) (k : Fin (2 ^ j + 1)) : gridPoint j k ∈ Icc (0 : ℝ) 1 := by
  refine ⟨gridPoint_nonnegative _ _, ?_⟩
  unfold gridPoint
  apply (div_le_one (pow_pos (by norm_num : (0 : ℝ) < 2) j)).2
  exact_mod_cast Nat.le_of_lt_succ k.isLt

lemma lifted_gridMaximum_zero_le (f : Ω → ℝ → ℝ) (ω : Ω) :
    gridMaximum (liftProcess f) 0 ω ≤ |f ω 0| + |f ω 1| := by
  apply maxAbs_le (add_nonneg (abs_nonneg _) (abs_nonneg _))
  intro k
  have hk : k.val = 0 ∨ k.val = 1 := by have := k.isLt; norm_num at this; omega
  rw [lifted_gridDeviation]
  rcases hk with hk | hk
  · simpa only [gridPoint, hk, Nat.cast_zero, pow_zero, zero_div] using le_add_of_nonneg_right (abs_nonneg (f ω 1))
  · simpa only [gridPoint, hk, Nat.cast_one, pow_zero, one_div_one] using le_add_of_nonneg_left (abs_nonneg (f ω 0))

lemma lifted_gridMaximum_le_chain (f : Ω → ℝ → ℝ) (ω : Ω) (J : ℕ) :
    gridMaximum (liftProcess f) J ω ≤ |f ω 0| + |f ω 1| +
      ∑ j ∈ Finset.range J, levelMaximum (liftProcess f) j ω := by
  induction J with
  | zero => simpa only [Finset.sum_range_zero, add_zero] using lifted_gridMaximum_zero_le f ω
  | succ J ih =>
    calc
      _ ≤ gridMaximum (liftProcess f) J ω + levelMaximum (liftProcess f) J ω := gridMaximum_succ_le _ _ _
      _ ≤ (|f ω 0| + |f ω 1| + ∑ j ∈ Finset.range J, levelMaximum (liftProcess f) j ω) +
          levelMaximum (liftProcess f) J ω := add_le_add ih le_rfl
      _ = _ := by rw [Finset.sum_range_succ]; ring

lemma gridMaximum_monotone (F : Ω → ℝ → ℝ) (ω : Ω) : Monotone (fun j ↦ gridMaximum F j ω) := by
  apply monotone_nat_of_le_succ
  intro j
  apply maxAbs_le (maxAbs_nonnegative _ _)
  intro k
  let l : Fin (2 ^ (j + 1) + 1) := ⟨2 * k.val, by have := k.isLt; rw [pow_succ]; omega⟩
  have hPoint : gridDeviation F (j + 1) l ω = gridDeviation F j k ω := by
    simp only [gridDeviation, l, gridPoint_even]
  simpa only [hPoint] using le_maxAbs (fun i : Fin (2 ^ (j + 1) + 1) ↦ gridDeviation F (j + 1) i) ω l

lemma exists_dyadic_approximation {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ k : ℕ → ℕ, (∀ j, k j ≤ 2 ^ j) ∧ Tendsto (fun j ↦ gridPoint j (k j)) atTop (𝓝 t) := by
  by_cases ht0 : t = 0
  · subst t
    exact ⟨fun _ ↦ 0, fun _ ↦ Nat.zero_le _, by simpa only [gridPoint, Nat.cast_zero, zero_div] using tendsto_const_nhds⟩
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  choose k hLeft hRight using (fun j : ℕ ↦ exists_grid_cell (2 ^ j) (by positivity) htp ht.2)
  refine ⟨fun j ↦ (k j).val, fun j ↦ (k j).isLt.le, ?_⟩
  have hRate : Tendsto (fun j : ℕ ↦ 1 / (2 : ℝ) ^ j) atTop (𝓝 0) := by
    simpa only [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hLeft' (j : ℕ) : gridPoint j (k j).val < t := by
    simpa only [gridPoint, Nat.cast_pow, Nat.cast_ofNat] using hLeft j
  have hRight' (j : ℕ) : t ≤ gridPoint j (k j).val + 1 / (2 : ℝ) ^ j := by
    have h := hRight j
    rw [add_div] at h
    simpa only [gridPoint, Nat.cast_pow, Nat.cast_ofNat] using h
  have hSmall : Tendsto (fun j ↦ t - gridPoint j (k j).val) atTop (𝓝 0) := by
    apply squeeze_zero (fun j ↦ sub_nonneg.mpr (hLeft' j).le) _ hRate
    intro j
    linarith [hRight' j]
  have hLim := (tendsto_const_nhds (x := t)).sub hSmall
  simp only [sub_zero] at hLim
  convert hLim using 1
  funext j
  ring

lemma continuousOn_le_of_dyadic_bounds {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    {B : ℝ} (hB : ∀ j (k : Fin (2 ^ j + 1)), |f (gridPoint j k)| ≤ B) :
    ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ B := by
  intro t ht
  obtain ⟨k, hk, hLim⟩ := exists_dyadic_approximation ht
  have hWithin : Tendsto (fun j ↦ gridPoint j (k j)) atTop (𝓝[Icc (0 : ℝ) 1] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hLim, Filter.Eventually.of_forall (fun j ↦
      gridPoint_mem_unitInterval j ⟨k j, Nat.lt_succ_of_le (hk j)⟩)⟩
  have hfLim := (hf t ht).tendsto.comp hWithin
  exact le_of_tendsto hfLim.abs (Filter.Eventually.of_forall (fun j ↦ hB j ⟨k j, Nat.lt_succ_of_le (hk j)⟩))

end ProphetSecretary.Analysis
