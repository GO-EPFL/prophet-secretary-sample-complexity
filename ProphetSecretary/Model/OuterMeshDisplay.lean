import ProphetSecretary.Model.Rounding

/-!
# The normalized outer mesh display

The display first normalizes by H and then rounds on the unit mesh. Clamping
outside the nonnegative unit interval totalizes arbitrary raw observations.
On nonnegative observations and H>0 this is exactly cap, mesh H/m, and divide by H.
-/

open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Model

noncomputable def outerUnitMesh (m : ℕ) (x : ℝ) : ℝ :=
  meshRound 1 m (min (max 0 x) 1)

lemma measurable_outerUnitMesh (m : ℕ) : Measurable (outerUnitMesh m) :=
  (measurable_meshRound 1 m).comp ((measurable_const.max measurable_id).min measurable_const)

lemma outerUnitMesh_mem_unit (m : ℕ) (hm : 0<m) (x : ℝ) : outerUnitMesh m x∈Icc (0:ℝ) 1 := by
  have hIn : min (max 0 x) 1∈Icc (0:ℝ) 1 :=
    ⟨le_min (le_max_left _ _) zero_le_one,min_le_right _ _⟩
  have hBounds := meshRound_bounds 1 (by norm_num) m hm hIn
  exact ⟨hBounds.1,hBounds.2.1.trans hIn.2⟩

lemma outerUnitMesh_mem_grid (m : ℕ) (hm : 0<m) (x : ℝ) : outerUnitMesh m x∈meshGrid 1 m :=
  meshRound_mem_meshGrid 1 (by norm_num) m hm
    ⟨le_min (le_max_left _ _) zero_le_one,min_le_right _ _⟩

@[simp] lemma outerUnitMesh_zero (m : ℕ) : outerUnitMesh m 0=0 := by
  simp [outerUnitMesh]

@[simp] lemma outerUnitMesh_one (m : ℕ) : outerUnitMesh m 1=1 := by
  unfold outerUnitMesh
  rw [max_eq_right (show (0:ℝ)≤1 by norm_num),min_self]
  exact meshRound_cap 1 m

noncomputable def outerMeshDisplay (m : ℕ) (H x : ℝ) : ℝ := outerUnitMesh m (x/H)

lemma measurable_outerMeshDisplay (m : ℕ) : Measurable (fun p : ℝ × ℝ => outerMeshDisplay m p.1 p.2) :=
  (measurable_outerUnitMesh m).comp (measurable_snd.div measurable_fst)

@[simp] lemma outerMeshDisplay_zero (m : ℕ) (H : ℝ) : outerMeshDisplay m H 0=0 := by
  simp [outerMeshDisplay]

lemma outerMeshDisplay_ge_cap (m : ℕ) {H x : ℝ} (hH : 0<H) (hx : H≤x) :
    outerMeshDisplay m H x=1 := by
  have hDiv : 1≤x/H := (le_div_iff₀ hH).mpr (by simpa only [one_mul] using hx)
  unfold outerMeshDisplay outerUnitMesh
  rw [max_eq_right (zero_le_one.trans hDiv),min_eq_right hDiv]
  exact meshRound_cap 1 m

lemma outerMeshDisplay_eq_mesh (m : ℕ) (H : ℝ≥0) (hH : (0:ℝ)<H) {x : ℝ} (hx : 0≤x) :
    outerMeshDisplay m H x=meshRound H m (capValue H x)/(H:ℝ) := by
  by_cases hcap : (H:ℝ)≤x
  · rw [outerMeshDisplay_ge_cap m hH hcap]
    simp only [capValue,min_eq_right hcap,meshRound_cap,div_self (ne_of_gt hH)]
  · have hxH : x<(H:ℝ) := lt_of_not_ge hcap
    have hDiv : x/(H:ℝ)<1 := (div_lt_one hH).mpr hxH
    have hDiv0 : 0≤x/(H:ℝ) := div_nonneg hx hH.le
    simp only [outerMeshDisplay,outerUnitMesh,max_eq_right hDiv0,min_eq_left hDiv.le,
      meshRound,NNReal.coe_one,not_le.mpr hDiv,if_false,capValue,min_eq_left hxH.le,
      hcap,one_div]
    field_simp

end ProphetSecretary.Model
