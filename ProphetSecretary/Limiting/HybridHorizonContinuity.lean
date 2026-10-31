import ProphetSecretary.Limiting.HybridHorizon
import ProphetSecretary.Limiting.WeakHybridValue

/-!
# Continuity of the actual finite-hybrid remaining-horizon value

Weak continuity of the scaled finite intensity is combined with the uniform
all-duration-weight value theorem. Varying the duration coefficient costs at
most its absolute change, since every normalized duration lies in [0,1].
No value at horizon zero is prescribed and no optimizer is assumed.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma FiniteIntensityHybridInstance.optimalScalarValue_duration_error
    (B : FiniteIntensityHybridInstance n) (w d e : ℝ) :
    B.optimalScalarValue w d ≤ B.optimalScalarValue w e+|d-e| := by
  apply csSup_le (B.scalarPayoffs_nonempty w d)
  rintro _ ⟨π,rfl⟩
  have hT0 := π.expectedDuration_nonnegative B
  have hT1 := π.expectedDuration_le_one B
  have hTerm : (d-e)*π.expectedDuration B ≤ |d-e| :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hT0).trans
      ((mul_le_mul_of_nonneg_left hT1 (abs_nonneg _)).trans_eq (mul_one _))
  have hPolicy : π.scalarObjective B w d ≤ π.scalarObjective B w e+|d-e| := by
    rw [π.scalarObjective_eq,π.scalarObjective_eq]
    linarith
  exact hPolicy.trans (add_le_add (B.scalarObjective_le_value π w e) le_rfl)

lemma FiniteIntensityHybridInstance.optimalScalarValue_duration_abs_sub_le
    (B : FiniteIntensityHybridInstance n) (w d e : ℝ) :
    |B.optimalScalarValue w d-B.optimalScalarValue w e| ≤ |d-e| := by
  have hde := B.optimalScalarValue_duration_error w d e
  have hed := B.optimalScalarValue_duration_error w e d
  rw [abs_sub_comm e d] at hed
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma FiniteIntensityHybridInstance.continuationValue_tendsto
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    {us : ℕ → ℝ≥0} {u : ℝ≥0} (hu : Tendsto us atTop (𝓝 u)) :
    Tendsto (fun m => B.continuationValue w c (us m)) atTop (𝓝 (B.continuationValue w c u)) := by
  let Bs := fun m => B.remainingHorizon (us m)
  let C := B.remainingHorizon u
  let ds := fun m => c*(us m : ℝ)
  let d := c*(u : ℝ)
  have hInt : Tendsto (fun m => (Bs m).intensity) atTop (𝓝 C.intensity) := hu.smul tendsto_const_nhds
  have hI : ∀ i, Tendsto (fun m => (Bs m).individuals.marginalProbabilityLaw i) atTop
      (𝓝 (C.individuals.marginalProbabilityLaw i)) := fun _ => tendsto_const_nhds
  have hWeak := optimalScalarValue_uniform_weak Bs C B.cap ⟨w,hw⟩ (fun _ => le_rfl) le_rfl
    (fun _ => rfl) hI hInt
  have hDiff : Tendsto (fun m => (Bs m).optimalScalarValue w (ds m)-C.optimalScalarValue w (ds m)) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hWeak ε hε] with m hm
    simpa only [Real.dist_eq,sub_zero] using hm w (ds m) hw le_rfl (mul_nonneg hc (us m).property)
  have hds : Tendsto ds atTop (𝓝 d) := (NNReal.tendsto_coe.2 hu).const_mul c
  have hAbs : Tendsto (fun m => |ds m-d|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,abs_zero] using (hds.sub_const d).abs
  have hFixed : Tendsto (fun m => C.optimalScalarValue w (ds m)) atTop (𝓝 (C.optimalScalarValue w d)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hAbs
    intro m
    simpa only [Real.norm_eq_abs] using C.optimalScalarValue_duration_abs_sub_le w (ds m) d
  have h := hDiff.add hFixed
  simpa only [sub_add_cancel,zero_add,Bs,C,ds,d,FiniteIntensityHybridInstance.continuationValue] using h

/-- Finite-hybrid continuation is continuous, including horizon zero, where
retained offer opportunities may give strictly positive value. -/
theorem FiniteIntensityHybridInstance.continuous_continuationValue
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Continuous (B.continuationValue w c) := by
  apply continuous_iff_seqContinuous.mpr
  intro us u hu
  exact B.continuationValue_tendsto hw hc hu

end ProphetSecretary.Limiting
