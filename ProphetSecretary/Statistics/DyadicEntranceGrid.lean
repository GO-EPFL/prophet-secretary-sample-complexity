import ProphetSecretary.Analysis.DyadicPath

/-!
# Dyadic observation grids approaching every later time

The sequence is extended constantly after its last preterminal grid point so
it is monotone on all natural indices. Every point is in [0,1). Existing dyadic
approximation gives eventual grid points inside any nonempty subinterval,
without new floor or rounding infrastructure.
-/

open Set Filter
open scoped Topology

namespace ProphetSecretary.Statistics

open ProphetSecretary.Reach.EmpiricalChaining

noncomputable def dyadicEntranceGrid (m j : ℕ) : ℝ := gridPoint m (min j (2^m-1))

lemma dyadicEntranceGrid_monotone (m : ℕ) : Monotone (dyadicEntranceGrid m) := by
  intro j k hjk
  unfold dyadicEntranceGrid gridPoint
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast min_le_min_right (2^m-1) hjk

lemma dyadicEntranceGrid_of_lt (m j : ℕ) (hj : j<2^m) : dyadicEntranceGrid m j = gridPoint m j := by
  unfold dyadicEntranceGrid
  rw [min_eq_left (by omega : j ≤ 2^m-1)]

lemma dyadicEntranceGrid_mem (m j : ℕ) : dyadicEntranceGrid m j ∈ Ico (0 : ℝ) 1 := by
  have hN : 0 < 2^m := by positivity
  have hk : min j (2^m-1) < 2^m := by omega
  unfold dyadicEntranceGrid gridPoint
  exact ⟨div_nonneg (Nat.cast_nonneg _) (by positivity),
    (div_lt_one (by positivity : (0 : ℝ) < (2:ℝ)^m)).mpr (by exact_mod_cast hk)⟩

/-- Every sufficiently fine grid meets any nonempty preterminal interval. -/
theorem eventually_dyadicEntranceGrid_between {r s : ℝ} (hr : 0 ≤ r) (hrs : r<s) (hs : s≤1) :
    ∀ᶠ m in atTop, ∃ j<2^m, r < dyadicEntranceGrid m j ∧ dyadicEntranceGrid m j < s := by
  let b := (r+s)/2
  have hb : b ∈ Icc (0 : ℝ) 1 := by dsimp [b]; constructor <;> linarith
  have hbrs : b ∈ Ioo r s := by dsimp [b]; constructor <;> linarith
  obtain ⟨k,hk,hlim⟩ := ProphetSecretary.Analysis.exists_dyadic_approximation hb
  have hnear : ∀ᶠ m in atTop, gridPoint m (k m) ∈ Ioo r s := hlim.eventually (isOpen_Ioo.mem_nhds hbrs)
  exact hnear.mono fun m hm => by
    have hlt : gridPoint m (k m) < 1 := hm.2.trans_le hs
    have hCast : (k m : ℝ) < (2:ℝ)^m := (div_lt_one (by positivity : (0 : ℝ) < (2:ℝ)^m)).mp hlt
    have hNat : k m < 2^m := by exact_mod_cast hCast
    refine ⟨k m,hNat,?_⟩
    simpa only [dyadicEntranceGrid_of_lt m (k m) hNat,Set.mem_Ioo] using hm

end ProphetSecretary.Statistics
