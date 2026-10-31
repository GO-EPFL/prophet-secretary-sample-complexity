import ProphetSecretary.Limiting.ClosureCompensatedIntensityFinite
import ProphetSecretary.Limiting.FiniteBandScaling
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Residual test integrals before and after band scaling

These identities concern the actual finite product marginals; the displayed
intensity multiplier is compared with the full complement compensation.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical BigOperators NNReal ENNReal
namespace ProphetSecretary.Limiting

lemma integral_labeledBandResidual {n : ℕ} (P : Model.Instance n) (N : ℕ) (d : ℝ) (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(labeledBandResidual P N d : Measure ℝ))=
      ∑ j∈Finset.univ.filter (fun j : Fin n => N≤j.val), ∫ x in Ioi d, f x ∂P.law j := by
  unfold labeledBandResidual
  rw [FiniteMeasure.toMeasure_sum,integral_finsetSum_measure (fun j _ => f.integrable _)]
  rfl

lemma integrable_bandTest (μ : Measure ℝ) [IsFiniteMeasure μ] {S : Set ℝ}
    (hS : MeasurableSet S) (θ : ℝ) (f : ℝ →ᵇ ℝ) :
    Integrable (fun x => (1+θ*S.indicator (fun _ => (1 : ℝ)) x)*f x) μ := by
  have h := (f.integrable μ).add (((f.integrable μ).indicator hS).const_mul θ)
  apply h.congr
  apply Eventually.of_forall
  intro x
  change f x+θ*S.indicator f x=(1+θ*S.indicator (fun _ => (1 : ℝ)) x)*f x
  by_cases hx : x∈S <;> simp [hx,add_mul]

lemma integral_bandScaledIntensity_multiplier (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (θ : ℝ) (hθ : 0≤1+θ) (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(bandScaledIntensity μ S ⟨1+θ,hθ⟩ : Measure ℝ))=
      ∫ x, (1+θ*S.indicator (fun _ => (1 : ℝ)) x)*f x ∂(μ : Measure ℝ) := by
  rw [bandScaledIntensity_toMeasure μ hS]
  have h := integral_withDensity_eq_integral_toReal_smul (μ := (μ : Measure ℝ))
    (ENNReal.measurable_ofReal.comp (measurable_bandScaleFactor hS ⟨1+θ,hθ⟩))
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun x => f x)
  apply h.trans
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change (ENNReal.ofReal (bandScaleFactor S (⟨1+θ,hθ⟩ : ℝ≥0) x)).toReal • f x=
    (1+θ*S.indicator (fun _ => (1 : ℝ)) x)*f x
  rw [ENNReal.toReal_ofReal (bandScaleFactor_nonnegative S (⟨1+θ,hθ⟩ : ℝ≥0) x),smul_eq_mul]
  by_cases hx : x∈S
  · rw [bandScaleFactor,if_pos hx,Set.indicator_of_mem hx]
    change (1+θ)*f x=(1+θ*1)*f x
    ring
  · rw [bandScaleFactor,if_neg hx,Set.indicator_of_notMem hx]
    simp only [mul_zero,add_zero]

lemma integral_bandScaled_labeledBandResidual {n : ℕ} (P : Model.Instance n) (N : ℕ) (d : ℝ)
    {S : Set ℝ} (hS : MeasurableSet S) (θ : ℝ) (hθ : 0≤1+θ) (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(bandScaledIntensity (labeledBandResidual P N d) S ⟨1+θ,hθ⟩ : Measure ℝ))=
      ∑ j∈Finset.univ.filter (fun j : Fin n => N≤j.val),
        ∫ x in Ioi d, (1+θ*S.indicator (fun _ => (1 : ℝ)) x)*f x ∂P.law j := by
  rw [integral_bandScaledIntensity_multiplier _ hS θ hθ f]
  unfold labeledBandResidual
  rw [FiniteMeasure.toMeasure_sum,integral_finsetSum_measure
    (fun j _ => integrable_bandTest _ hS θ f)]
  rfl

lemma integral_compensatedResidualOffers {n : ℕ} (P : Model.Instance n) (N : ℕ) (d : ℝ)
    {S : Set ℝ} (hS : MeasurableSet S) (θ : ℝ) (hθ : |θ|≤1/4)
    (hSmall : ResidualBandSmall P N S) (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(labeledBandResidual (compensatedResidualOffers P N S hS θ hθ) N d : Measure ℝ))=
      ∑ j∈Finset.univ.filter (fun j : Fin n => N≤j.val),
        ∫ x in Ioi d, f x ∂ProphetSecretary.Probability.tiltLaw (P.law j)
          (ProphetSecretary.Probability.compensatedBandScore (P.law j) S) θ := by
  rw [integral_labeledBandResidual]
  apply Finset.sum_congr rfl
  intro j hj
  rw [compensatedResidualOffers_law_residual P N hS θ hθ hSmall j (Finset.mem_filter.mp hj).2]

end ProphetSecretary.Limiting
