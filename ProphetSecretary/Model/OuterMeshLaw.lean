import ProphetSecretary.Statistics.OuterTransformedTraining

/-!
# The fixed-cutoff normalized mesh law

The law sampled by fresh transformed observations is exactly the capped mesh
instance scaled by 1/H. Its prophet value and positive count therefore satisfy
the quantitative eligibility comparisons used in the outer reduction.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Model.Instance
variable {n : ℕ}

lemma outerTransformedInstance_eq_scale_mesh (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (hH : (0:ℝ)<H) :
    P.outerTransformedInstance m hm t H=
      ((P.retainedAtTag t).meshCap H hH m hm).scale (1/(H:ℝ)) (by positivity) := by
  apply ext_law
  funext i
  change ((P.retainedAtTag t).law i).map (outerMeshDisplay m H)=
    ((((P.retainedAtTag t).law i).map (capValue H)).map (meshRound H m)).map (fun x => (1/(H:ℝ))*x)
  have hScale : Measurable (fun x : ℝ => (1/(H:ℝ))*x) := measurable_const.mul measurable_id
  rw [Measure.map_map hScale (measurable_meshRound H m),
    Measure.map_map (hScale.comp (measurable_meshRound H m)) (measurable_capValue H)]
  apply Measure.map_congr
  filter_upwards [(P.retainedAtTag t).nonnegative i] with x hx
  rw [outerMeshDisplay_eq_mesh m H hH hx]
  simp only [Function.comp_apply,div_eq_mul_inv]
  ring

lemma outerTransformedInstance_expectedMaximum (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (hH : (0:ℝ)<H) :
    (P.outerTransformedInstance m hm t H).expectedMaximum=
      ((P.retainedAtTag t).meshCap H hH m hm).expectedMaximum/(H:ℝ) := by
  rw [P.outerTransformedInstance_eq_scale_mesh m hm t H hH,scale_expectedMaximum]
  ring

lemma outerTransformedInstance_mean_bounds (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (hH : (0:ℝ)<H) :
    ((P.retainedAtTag t).cap H).expectedMaximum/(H:ℝ)-1/(m:ℝ)≤
      (P.outerTransformedInstance m hm t H).expectedMaximum ∧
    (P.outerTransformedInstance m hm t H).expectedMaximum≤
      ((P.retainedAtTag t).cap H).expectedMaximum/(H:ℝ) := by
  have h := (P.retainedAtTag t).meshCap_expectedMaximum_bounds H hH m hm
  rw [P.outerTransformedInstance_expectedMaximum m hm t H hH]
  constructor
  · have hDiv := div_le_div_of_nonneg_right h.1 hH.le
    calc
      _ = (((P.retainedAtTag t).cap H).expectedMaximum-(H:ℝ)/(m:ℝ))/(H:ℝ) := by
        field_simp [ne_of_gt hH]
      _ ≤ _ := hDiv
  · exact div_le_div_of_nonneg_right h.2 hH.le

lemma outerTransformedInstance_positiveCount_le (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) {H : ℝ} (hH : 0<H) :
    (P.outerTransformedInstance m hm t H).positiveCount≤(P.retainedAtTag t).positiveCount := by
  unfold positiveCount tailCount
  apply Finset.sum_le_sum
  intro i _
  change (((P.retainedAtTag t).law i).map (outerMeshDisplay m H)).real (Ioi 0)≤_
  have hD : Measurable (outerMeshDisplay m H) := (measurable_outerUnitMesh m).comp (measurable_id.div_const H)
  rw [map_measureReal_apply hD measurableSet_Ioi]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  change 0<outerMeshDisplay m H x at hx
  change 0<x
  by_contra h
  have hx0 : x≤0 := le_of_not_gt h
  have hDiv : x/H≤0 := div_nonpos_of_nonpos_of_nonneg hx0 hH.le
  have hZero : outerMeshDisplay m H x=0 := by
    unfold outerMeshDisplay outerUnitMesh
    rw [max_eq_left hDiv,min_eq_left zero_le_one,meshRound_zero]
  simp only [hZero,lt_self_iff_false] at hx

end ProphetSecretary.Model.Instance
