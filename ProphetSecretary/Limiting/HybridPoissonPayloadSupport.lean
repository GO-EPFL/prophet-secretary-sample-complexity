import ProphetSecretary.Limiting.HybridPoissonPayloadEnvelope

/-!
# The fixed base optimizer gives a supporting payoff

The verified base canonical policy belongs to the common tagged class. Its
actual selected coefficient therefore gives a global affine lower bound
throughout the explicit positive-support radius.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open CountableInstance
variable {n : ℕ} {T : Type} [MeasurableSpace T] [StandardBorelSpace T]

lemma FiniteIntensityHybridInstance.poissonPayloadValuePath_ge_support
    (B : FiniteIntensityHybridInstance n) (hZero : B.terminal=0)
    {w c D b θ : ℝ} (hw : 0<w) (hc : 0<c) (hD : 0≤D) (hb : 0<b)
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) (A : ℝ × T → ℝ) (hA : Measurable A)
    (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0)
    (hθ : |θ|≤ individualValueRadius D b) :
    B.optimalScalarValue w c+θ*(w*canonicalChronologicalAmplitudeMean B κ A w c)≤
      (B.poissonPayloadValuePath κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c := by
  let π₀ := (B.valueThresholdPolicy hw.le hc.le).observePayload (Prod.fst : ℝ × T → ℝ) measurable_fst
  have hOpt : (π₀.sampleTags κ).scalarObjective B w c=B.optimalScalarValue w c :=
    ((B.valueThresholdPolicy hw.le hc.le).observePayload_fst_scalarObjective B hZero κ w c).trans
      (B.valueThresholdPolicy_optimal hZero hw hc.le)
  obtain ⟨ψ,_hψ,_hMono,hψZero,_hLim,hCoefficient⟩ :=
    tagged_hybrid_coefficient_stability (T := T) (fun _ : Unit => n) (fun _ => B)
      B.cap.property hw hc hD hb (fun _ => hZero) (fun _ => le_rfl)
      B.tailCount (fun d _ => B.tailCount_nonnegative d) (fun _ _ _ => le_rfl)
  have hCoeff₀ : π₀.payloadAmplitudeMean B κ t0 A=canonicalChronologicalAmplitudeMean B κ A w c := by
    have h := hCoefficient κ t0 A hA hBound hVanish () π₀
    rw [hOpt,sub_self,hψZero] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  let J := fun π : RandomizedTaggedHybridPolicy n T =>
    (π.sampleTags κ).scalarObjective B w c+θ*(w*π.payloadAmplitudeMean B κ t0 A)
  have hBdd : BddAbove (range J) := by
    refine ⟨B.optimalScalarValue w c+|θ| * (w*D),?_⟩
    rintro _ ⟨π,rfl⟩
    have hBase := B.scalarObjective_le_value (π.sampleTags κ) w c
    have hMean := π.payloadAmplitudeMean_abs_le B κ t0 A hD hBound
    have hDerv : |w*π.payloadAmplitudeMean B κ t0 A|≤w*D := by
      rw [abs_mul,abs_of_pos hw]
      exact mul_le_mul_of_nonneg_left hMean hw.le
    have hTerm : θ*(w*π.payloadAmplitudeMean B κ t0 A)≤|θ| * (w*D) :=
      (le_abs_self _).trans ((abs_mul _ _).le.trans
        (mul_le_mul_of_nonneg_left hDerv (abs_nonneg θ)))
    exact add_le_add hBase hTerm
  have h := le_csSup hBdd (mem_range_self π₀)
  dsimp only [J] at h
  rw [hOpt,hCoeff₀] at h
  simpa only [← B.poissonPayloadValuePath_value_eq_sSup hZero κ t0 A hA hD hb hBound hVanish hθ w c] using h

end ProphetSecretary.Limiting
