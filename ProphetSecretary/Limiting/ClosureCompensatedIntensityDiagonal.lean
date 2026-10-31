import ProphetSecretary.Limiting.ClosureCompensatedIntensityMaximum
import ProphetSecretary.Limiting.ClosureCompensatedIntensityIntegrals
import ProphetSecretary.Limiting.WeakCapBandScaling
import ProphetSecretary.Limiting.LabeledResidualData
import ProphetSecretary.Probability.CompensatedCloudTestError

/-!
# Weak limit of the actual compensated residual diagonal

The complement error is bounded by the largest residual band probability
multiplied by a bounded tail mass. Thus only the intended band multiplier
survives, uniformly in the number of existing finite labels.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

 theorem compensatedResidualOffers_diagonal_tendsto {sizes : ℕ → ℕ}
    (P : ∀ m, Model.Instance (sizes m)) (Ns : ℕ → ℕ) (H : ℝ≥0)
    (hCap : ∀ m j, ∀ᵐ x ∂(P m).law j, x≤(H : ℝ))
    {S : Set ℝ} (hS : MeasurableSet S) (θ : ℝ) (hθ : |θ|≤1/4)
    (hRare : ∀ ε>(0 : ℝ), ∀ᶠ m in atTop, ∀ j : Fin (sizes m), Ns m≤j.val → ((P m).law j).real S<ε)
    {d : ℝ} (hd : 0≤d) {K : ℝ} (hTail : ∀ m, (P m).tailCount d≤K)
    {μ : FiniteMeasure ℝ}
    (hWeak : Tendsto (fun m => labeledBandResidual (P m) (Ns m) d) atTop (𝓝 μ))
    (hμCap : ∀ᵐ x ∂(μ : Measure ℝ), x∈Icc (0 : ℝ) H)
    (hCont : ∀ᵐ x ∂(μ : Measure ℝ),
      ContinuousWithinAt (S.indicator (fun _ : ℝ => (1 : ℝ))) (Icc (0 : ℝ) H) x) :
    Tendsto (fun m => labeledBandResidual (compensatedResidualOffers (P m) (Ns m) S hS θ hθ) (Ns m) d)
      atTop (𝓝 (bandScaledIntensity μ S ⟨1+θ,by have := (abs_le.mp hθ).1; linarith⟩)) := by
  let r : ℝ≥0 := ⟨1+θ,by have := (abs_le.mp hθ).1; linarith⟩
  have hCaps (m : ℕ) : ∀ᵐ x ∂(labeledBandResidual (P m) (Ns m) d : Measure ℝ), x∈Icc (0 : ℝ) H :=
    (labeledBandResidual_supported (P m) (Ns m) d H (hCap m)).mono (fun _ hx => ⟨hd.trans hx.1,hx.2⟩)
  have hIdeal := bandScaledIntensity_tendsto_of_cap_relative_continuity H hCaps hμCap hWeak hS r hCont
  let p := fun m => (residualBandMaximum (P m) (Ns m) S : ℝ)
  have hp0 (m : ℕ) : 0≤p m := (residualBandMaximum (P m) (Ns m) S).property
  have hpLim : Tendsto p atTop (𝓝 0) := residualBandMaximum_tendsto_zero P Ns S hRare
  have hpHalf : ∀ᶠ m in atTop, p m≤1/2 := hpLim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2)) |>.mono (fun _ h => h.le)
  have hSmall : ∀ᶠ m in atTop, ResidualBandSmall (P m) (Ns m) S := hpHalf.mono (fun m hm j hj =>
    (residualBandMaximum_bounds (P m) (Ns m) S j hj).trans hm)
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  let A := fun m => ∫ x, f x ∂(labeledBandResidual (compensatedResidualOffers (P m) (Ns m) S hS θ hθ) (Ns m) d : Measure ℝ)
  let Z := fun m => ∫ x, f x ∂(bandScaledIntensity (labeledBandResidual (P m) (Ns m) d) S r : Measure ℝ)
  have hError : ∀ᶠ m in atTop, |A m-Z m|≤2*|θ| * p m*‖f‖*K := by
    filter_upwards [hpHalf,hSmall] with m hm hSm
    have hTest := compensatedCloud_test_error_le (D := Ioi d) ((P m).law)
      (Finset.univ.filter (fun j : Fin (sizes m) => Ns m≤j.val)) hS measurableSet_Ioi f
      (hp0 m) hm (fun j hj => residualBandMaximum_bounds (P m) (Ns m) S j (Finset.mem_filter.mp hj).2) hθ
    have hMass : (∑ j∈Finset.univ.filter (fun j : Fin (sizes m) => Ns m≤j.val), ((P m).law j).real (Ioi d))≤K := by
      apply le_trans _ (hTail m)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => measureReal_nonneg)
    dsimp only [A,Z]
    rw [integral_compensatedResidualOffers _ _ _ hS θ hθ hSm f,
      integral_bandScaled_labeledBandResidual _ _ _ hS θ r.property f]
    exact hTest.trans (mul_le_mul_of_nonneg_left hMass
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg θ)) (hp0 m)) (norm_nonneg f)))
  have hEnvelope : Tendsto (fun m => 2*|θ| * p m*‖f‖*K) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using ((hpLim.const_mul (2*|θ|)).mul_const ‖f‖).mul_const K
  have hAbs : Tendsto (fun m => |A m-Z m|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hError hEnvelope
  have hDiff : Tendsto (fun m => A m-Z m) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs] using (tendsto_zero_iff_norm_tendsto_zero.mpr hAbs)
  have hZ := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hIdeal f
  change Tendsto Z atTop (𝓝 (∫ x, f x ∂(bandScaledIntensity μ S r : Measure ℝ))) at hZ
  have hSum := hDiff.add hZ
  simpa only [zero_add,sub_add_cancel] using hSum

end ProphetSecretary.Limiting
