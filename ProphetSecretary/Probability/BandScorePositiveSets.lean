import ProphetSecretary.Probability.BandScore

/-!
# Zero-atom likelihood tilts on measurable positive sets

Away from zero the score is the target-band indicator. Thus the actual
perturbed probability of any measurable set excluding zero changes by the
mass of its intersection with that band. All compensation remains at zero.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Probability

lemma bandScore_tilt_real_of_notMem_zero (κ : Measure ℝ) [IsProbabilityMeasure κ]
    {B S : Set ℝ} (hB : MeasurableSet B) (hB0 : (0:ℝ)∉B) (hS : MeasurableSet S) (hS0 : (0:ℝ)∉S)
    (hq : (1/2:ℝ)≤κ.real {0}) {θ : ℝ} (hθ : |θ|≤1/4) :
    (tiltLaw κ (bandScore κ B) θ).real S=κ.real S+θ*κ.real (S∩B) := by
  have hh := measurable_bandScore κ hB
  have hb : ∀ᵐ x ∂κ, |bandScore κ B x|≤1 := Filter.Eventually.of_forall (bandScore_abs_le_one κ hB0 hq)
  haveI := tiltLaw_probability hh hb (bandScore_mean κ hB hq) hθ
  have hInt := integral_indicator_const (μ := tiltLaw κ (bandScore κ B) θ) (1:ℝ) hS
  simp only [smul_eq_mul,mul_one] at hInt
  rw [← hInt,integral_tiltLaw hh (tiltFactor_ae_nonnegative hb hθ)]
  have hFun : (fun x => tiltFactor (bandScore κ B) θ x*S.indicator (fun _ : ℝ => (1:ℝ)) x)=
      (fun x => S.indicator (fun _ : ℝ => (1:ℝ)) x+θ*(S∩B).indicator (fun _ : ℝ => (1:ℝ)) x) := by
    funext x
    by_cases hxS : x∈S
    · have hx0 : x≠0 := fun hx => hS0 (hx ▸ hxS)
      by_cases hxB : x∈B <;> simp [tiltFactor,bandScore,Set.indicator,hxS,hxB,hx0]
    · simp [Set.indicator,hxS]
  rw [hFun,integral_add ((integrable_const 1).indicator hS)
    (((integrable_const 1).indicator (hS.inter hB)).const_mul θ),integral_const_mul,
    integral_indicator_const 1 hS,integral_indicator_const 1 (hS.inter hB)]
  simp only [smul_eq_mul,mul_one]
end ProphetSecretary.Probability
