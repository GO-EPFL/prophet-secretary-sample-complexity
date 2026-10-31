import ProphetSecretary.Model.Rounding

/-!
# The finite possible values for the bounded outer learner

The unit mesh is contained in [0,1] and includes 0 and 1, even if either
endpoint has zero probability in a particular transformed instance.
-/

open Set
open scoped Classical NNReal
namespace ProphetSecretary.Model

lemma meshGrid_unit_subset (m : ℕ) (hm : 0<m) : (meshGrid 1 m : Set ℝ)⊆Icc (0:ℝ) 1 := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  have hjN : j≤m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hjR : (j:ℝ)≤m := by exact_mod_cast hjN
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  change 0≤(1:ℝ)/(m:ℝ)*(j:ℝ) ∧ (1:ℝ)/(m:ℝ)*(j:ℝ)≤1
  constructor
  · positivity
  · have hEq : (1:ℝ)/(m:ℝ)*(j:ℝ)=(j:ℝ)/(m:ℝ) := by ring
    rw [hEq]
    exact (div_le_one hmR).mpr hjR

lemma meshGrid_unit_endpoints (m : ℕ) (hm : 0<m) :
    (0:ℝ)∈meshGrid 1 m ∧ (1:ℝ)∈meshGrid 1 m :=
  ⟨zero_mem_meshGrid 1 m,cap_mem_meshGrid 1 m hm⟩

end ProphetSecretary.Model
