import ProphetSecretary.Limiting.CountableSymmetricIndividualValue

/-!
# A fair individual perturbation above a fixed positive level

The amplitude is the indicator of `[b,∞)`. For `b>0` the displayed law uses
the certified radius `individualValueRadius 1 b` and ambient cap larger by
one. The actual symmetric-payload envelope gives scalar value change o(h),
with the latent independent sign revealed only at its occurrence.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def positiveLevelIndicator (b x : ℝ) : ℝ := if b≤x then 1 else 0

lemma measurable_positiveLevelIndicator (b : ℝ) : Measurable (positiveLevelIndicator b) :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma positiveLevelIndicator_mem_unit (b x : ℝ) : positiveLevelIndicator b x ∈ Icc (0 : ℝ) 1 := by
  unfold positiveLevelIndicator
  split_ifs <;> norm_num

lemma positiveLevelIndicator_abs_le_one (b x : ℝ) : |positiveLevelIndicator b x|≤1 := by
  rw [abs_of_nonneg (positiveLevelIndicator_mem_unit b x).1]
  exact (positiveLevelIndicator_mem_unit b x).2

lemma positiveLevelIndicator_vanish (b x : ℝ) (hx : x<b) : positiveLevelIndicator b x=0 :=
  if_neg (not_le.mpr hx)

noncomputable def symmetricLevelIndividualPath (B : CountableInstance) (i : ℕ) (b : ℝ)
    (hb : 0<b) (θ : ℝ) : CountableInstance :=
  B.symmetricIndividualValuePath i (positiveLevelIndicator b) (measurable_positiveLevelIndicator b) 1 b
    (by norm_num) hb (positiveLevelIndicator_abs_le_one b) (positiveLevelIndicator_vanish b) θ

theorem symmetricLevelIndividualPath_scalar_change_isLittleO (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : ℕ) (b : ℝ) (hb : 0<b) :
    (fun θ => (B.symmetricLevelIndividualPath i b hb θ).optimalScalarValue w c-B.optimalScalarValue w c)
      =o[𝓝 (0 : ℝ)] (fun θ => θ) :=
  B.symmetricIndividualValuePath_scalar_change_isLittleO hZero hw hc i (positiveLevelIndicator b)
    (measurable_positiveLevelIndicator b) (by norm_num) hb
    (positiveLevelIndicator_abs_le_one b) (positiveLevelIndicator_vanish b)

end ProphetSecretary.Limiting.CountableInstance
