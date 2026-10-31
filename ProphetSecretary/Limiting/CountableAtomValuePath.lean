import ProphetSecretary.Limiting.CountableCenteredPoissonNonnegative
import ProphetSecretary.Probability.AtomDisplacement

/-!
# Symmetrically splitting a positive Poisson atom

A fair independent sign moves precisely the occurrences of one fixed mark.
The actual pushforward intensity is the unchanged complement plus the two
shifted half-atoms. This is a bounded measurable positive-support payload.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Probability

noncomputable def atomAmplitude (x : ℝ) (z : ℝ × Bool) : ℝ :=
  if z.1=x then boolSign z.2 else 0

lemma measurable_atomAmplitude (x : ℝ) : Measurable (atomAmplitude x) :=
  ((measurable_of_finite boolSign).comp measurable_snd).piecewise
    ((measurableSet_singleton x).preimage measurable_fst) measurable_const

lemma atomAmplitude_bound (x : ℝ) (z : ℝ × Bool) : |atomAmplitude x z|≤1 := by
  unfold atomAmplitude boolSign
  split_ifs <;> norm_num

lemma atomAmplitude_vanish {x : ℝ} (hx : 0<x) (z : ℝ × Bool) (hz : z.1<x/2) :
    atomAmplitude x z=0 := by
  unfold atomAmplitude
  exact if_neg (by intro h; rw [h] at hz; linarith)

lemma atomAmplitude_centered (x y : ℝ) : (∫ s, atomAmplitude x (y,s) ∂fairBoolLaw)=0 := by
  by_cases hy : y=x
  · simp [atomAmplitude,hy]
    exact integral_boolSign
  · simp only [atomAmplitude,hy,if_false,integral_zero]

noncomputable def symmetricAtomPath (B : CountableInstance) (hZero : B.terminal=0)
    (x : ℝ) (hx : 0<x) (h : ℝ) : CountableInstance :=
  B.poissonPayloadValuePath hZero fairBoolLaw (atomAmplitude x) (measurable_atomAmplitude x)
    1 (x/2) (by norm_num) (half_pos hx) (atomAmplitude_bound x) (atomAmplitude_vanish hx) h

lemma symmetricAtomPath_intensity (B : CountableInstance) (hZero : B.terminal=0)
    (x : ℝ) (hx : 0<x) {h : ℝ} (hNear : |h|≤ individualValueRadius 1 (x/2)) :
    (B.symmetricAtomPath hZero x hx h).intensity=
      B.intensity.restrict {x}ᶜ+(B.intensity {x}/2) • Measure.dirac (x+h)+
        (B.intensity {x}/2) • Measure.dirac (x-h) := by
  change (B.intensity.prod fairBoolLaw).map (payloadValueDisplay (atomAmplitude x) 1 (x/2) h)=_
  have hMap : payloadValueDisplay (atomAmplitude x) 1 (x/2) h=signedAtomDisplay x h := by
    funext z
    rw [payloadValueDisplay,if_pos hNear]
    by_cases hz : z.1=x
    · simp [atomAmplitude,signedAtomDisplay,hz]
    · simp only [atomAmplitude,signedAtomDisplay,if_neg hz,mul_zero,add_zero]
  rw [hMap]
  exact map_signedAtomDisplay B.intensity x h

theorem symmetricAtomPath_scalar_change_isLittleO (B : CountableInstance)
    (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c) (x : ℝ) (hx : 0<x) :
    (fun h => (B.symmetricAtomPath hZero x hx h).optimalScalarValue w c-B.optimalScalarValue w c)
      =o[𝓝 (0 : ℝ)] (fun h => h) := by
  have hd := B.hasDerivAt_optimalScalarValue_centeredPoissonPayload hZero hw hc
    (by norm_num : (0 : ℝ)≤1) (half_pos hx) fairBoolLaw false (atomAmplitude x) (measurable_atomAmplitude x)
    (atomAmplitude_bound x) (atomAmplitude_vanish hx) (atomAmplitude_centered x)
  have hAtZero : (B.symmetricAtomPath hZero x hx 0).optimalScalarValue w c=B.optimalScalarValue w c := by
    change (B.poissonPayloadValuePath hZero fairBoolLaw (atomAmplitude x) (measurable_atomAmplitude x)
      1 (x/2) (by norm_num) (half_pos hx) (atomAmplitude_bound x) (atomAmplitude_vanish hx) 0).optimalScalarValue w c=_
    rw [B.poissonPayloadValuePath_zero]
    exact B.withCap_optimalScalarValue _ _ w c
  change HasDerivAt (fun h => (B.symmetricAtomPath hZero x hx h).optimalScalarValue w c) 0 0 at hd
  simpa only [hAtZero,sub_zero,smul_zero] using hasDerivAt_iff_isLittleO.mp hd

end ProphetSecretary.Limiting.CountableInstance
