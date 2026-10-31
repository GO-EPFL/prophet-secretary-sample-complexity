import ProphetSecretary.Limiting.ValueWeightedMeasure

/-!
# Continuous nonnegative weighting of marginal laws

A fixed bounded continuous nonnegative weight gives actual finite measures,
with weakly continuous weighting and exact integration identities. Unlike
value weighting, this construction applies to the above-reserve ordering
weight even when total first moments are unbounded.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal
namespace ProphetSecretary.Limiting

noncomputable def continuousWeightedLaw (p : ProbabilityMeasure ℝ) (w : ℝ →ᵇ ℝ) : FiniteMeasure ℝ := by
  refine ⟨(p : Measure ℝ).withDensity (fun x => ENNReal.ofReal (w x)),?_⟩
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc
    (∫⁻ x, ENNReal.ofReal (w x) ∂(p : Measure ℝ)) ≤ ∫⁻ _x, ENNReal.ofReal ‖w‖ ∂(p : Measure ℝ) :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal (w.apply_le_norm x)
    _ < ⊤ := by simp

lemma continuousWeightedLaw_mass (p : ProbabilityMeasure ℝ) (w : ℝ →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x) :
    ((continuousWeightedLaw p w).mass : ℝ) = ∫ x, w x ∂(p : Measure ℝ) := by
  have hm : ((continuousWeightedLaw p w).mass : ℝ) = ((continuousWeightedLaw p w : Measure ℝ) Set.univ).toReal := by
    simpa only [ENNReal.coe_toReal] using congrArg ENNReal.toReal (FiniteMeasure.ennreal_mass (μ := continuousWeightedLaw p w))
  rw [hm]
  change ((p : Measure ℝ).withDensity (fun x => ENNReal.ofReal (w x)) Set.univ).toReal = _
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hw) w.continuous.measurable.aestronglyMeasurable).symm

lemma continuousWeightedLaw_integral (p : ProbabilityMeasure ℝ) (w : ℝ →ᵇ ℝ)
    (hw : ∀ x, 0 ≤ w x) (f : ℝ → ℝ) :
    (∫ x, f x ∂(continuousWeightedLaw p w : Measure ℝ)) = ∫ x, w x * f x ∂(p : Measure ℝ) := by
  change (∫ x, f x ∂(p : Measure ℝ).withDensity (fun x => ENNReal.ofReal (w x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul w.continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hw x),smul_eq_mul]

lemma continuousWeightedLaw_supported_interval (p : ProbabilityMeasure ℝ) (w : ℝ →ᵇ ℝ)
    {H : ℝ} (hcap : (p : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    (continuousWeightedLaw p w : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 :=
  (withDensity_absolutelyContinuous _ _) hcap

lemma continuousWeightedLaw_dirac_zero (w : ℝ →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x) (hw0 : w 0 = 0) :
    continuousWeightedLaw (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) w = 0 := by
  apply (FiniteMeasure.mass_zero_iff _).mp
  have hm := continuousWeightedLaw_mass (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) w hw
  change _ = (∫ x, w x ∂Measure.dirac (0 : ℝ)) at hm
  rw [integral_dirac,hw0] at hm
  exact_mod_cast hm

theorem continuousWeightedLaw_tendsto {Γ : Type*} {l : Filter Γ}
    {ps : Γ → ProbabilityMeasure ℝ} {p : ProbabilityMeasure ℝ} (hp : Tendsto ps l (𝓝 p))
    (w : ℝ →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x) :
    Tendsto (fun m => continuousWeightedLaw (ps m) w) l (𝓝 (continuousWeightedLaw p w)) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  simp_rw [continuousWeightedLaw_integral _ w hw]
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hp) (w * f)

end ProphetSecretary.Limiting
