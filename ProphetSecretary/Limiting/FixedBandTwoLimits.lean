import ProphetSecretary.Limiting.WeightedBandStateWeak
import ProphetSecretary.Limiting.WeightedBandBenchmarkError
import ProphetSecretary.Limiting.HybridIntensityUniformError
import ProphetSecretary.Limiting.HybridIntensityBenchmarkLimit
import ProphetSecretary.Analysis.ReciprocalRank

/-!
# The two limits at a fixed positive cutoff above reserve

First the original finite-instance sequence tends to its extracted laws at
fixed N. Only afterwards is N increased to remove the residual individual
intensity. Both scalar values and benchmarks are actual model quantities.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators

namespace ProphetSecretary.Limiting

lemma fixed_band_scalar_two_limits (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (B : CountableInstance) (wgt : ℝ →ᵇ ℝ) (b W : ℝ≥0)
    (hb : (B.terminal : ℝ) < b) (hbH : b ≤ B.cap)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (B.cap : ℝ))
    (hwgt0 : ∀ x, 0 ≤ wgt x) (hwgtZero : wgt 0 = 0) (hwgt : Monotone wgt)
    (hWeight : ∀ m, (∑ i, ∫ x, wgt x ∂(P m).law i) ≤ 1) (hbPos : 0 < wgt b)
    (μs : ℕ → FiniteMeasure ℝ) (hμs : ∀ N, ∀ᵐ x ∂(μs N : Measure ℝ), x ∈ Ioc (0 : ℝ) B.cap)
    (hOrder : ∀ N, (B.intensityAbove b hb : Measure ℝ) ≤ (μs N : Measure ℝ))
    (hWeak : Tendsto μs atTop (𝓝 (B.intensityAbove b hb)))
    (hIndividuals : ∀ i, Tendsto (fun m => weightOrderedPaddedLaw (P m) wgt i) atTop (𝓝 (B.individuals i)))
    (hBands : ∀ N, Tendsto (fun m => weightOrderedBandResidual (P m) wgt N b) atTop (𝓝 (μs N))) :
    ∀ ε > (0 : ℝ), ∀ᶠ N in atTop, ∀ᶠ m in atTop, ∀ w c : ℝ,
      0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c →
      |Model.optimalTerminalScalarValue (P m) b w c-
        (B.prefixIntensityState N b hbH (B.intensityAbove b hb)
          (B.truncation N b hb).intensity_supported).optimalScalarValue w c| < ε := by
  let μ := B.intensityAbove b hb
  have hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) B.cap := (B.truncation 0 b hb).intensity_supported
  let Cs := fun N => B.prefixIntensityState N b hbH μ hμ
  let Ds := fun N => B.prefixIntensityState N b hbH (μs N) (hμs N)
  have hResidual := hybrid_intensity_uniform_error (fun N => N) Cs Ds μ B.cap W
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (hμ.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) hOrder hWeak
  have hRank : Tendsto (fun N : ℕ => (Real.pi/2)*(W : ℝ)*(B.cap : ℝ)*
      Real.sqrt (1/((wgt b)^2*(N+1 : ℕ)))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (ProphetSecretary.Analysis.sqrt_reciprocal_rank_tendsto_zero ((wgt b)^2)).const_mul
        ((Real.pi/2)*(W : ℝ)*(B.cap : ℝ))
  intro ε hε
  have hε3 : 0 < ε/3 := by positivity
  filter_upwards [hResidual (ε/3) hε3,(tendsto_order.mp hRank).2 (ε/3) hε3] with N hRes hSmall
  have hFinite := weightOrderedBandState_uniform_weak sizes P B wgt N b W hbH hcap
    (μs N) (hμs N) hIndividuals (hBands N) (ε/3) hε3
  filter_upwards [hFinite] with m hm
  intro w c hw hwW hc
  have hCausal := weightOrderedBandState_value_error_le (P m) wgt N B.cap b hbH (hcap m)
    hwgt0 hwgtZero (hWeight m) hbPos (fun x hx => hwgt hx.le) hw hc
  have hCoef : (Real.pi/2)*w*(B.cap : ℝ)*Real.sqrt (1/((wgt b)^2*(N+1 : ℕ))) ≤
      (Real.pi/2)*(W : ℝ)*(B.cap : ℝ)*Real.sqrt (1/((wgt b)^2*(N+1 : ℕ))) := by gcongr
  have hA := hCausal.trans_lt (hCoef.trans_lt hSmall)
  have hF := hm w c hw hwW hc
  have hR := hRes w c hw hwW hc
  change |Model.optimalTerminalScalarValue (P m) b w c-(Cs N).optimalScalarValue w c| < ε
  calc
    _ ≤ |Model.optimalTerminalScalarValue (P m) b w c-
        (weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)).optimalScalarValue w c|+
        |(weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)).optimalScalarValue w c-
          (Cs N).optimalScalarValue w c| := abs_sub_le _ _ _
    _ ≤ |Model.optimalTerminalScalarValue (P m) b w c-
        (weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)).optimalScalarValue w c|+
        (|(weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)).optimalScalarValue w c-
            (Ds N).optimalScalarValue w c|+|(Ds N).optimalScalarValue w c-(Cs N).optimalScalarValue w c|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ < ε := by linarith only [hA,hF,hR]

lemma fixed_band_benchmark_two_limits (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (B : CountableInstance) (wgt : ℝ →ᵇ ℝ) (b : ℝ≥0)
    (hb : (B.terminal : ℝ) < b) (hbH : b ≤ B.cap)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (B.cap : ℝ))
    (hwgt0 : ∀ x, 0 ≤ wgt x) (hwgtZero : wgt 0 = 0) (hwgt : Monotone wgt)
    (hWeight : ∀ m, (∑ i, ∫ x, wgt x ∂(P m).law i) ≤ 1) (hbPos : 0 < wgt b)
    (μs : ℕ → FiniteMeasure ℝ) (hμs : ∀ N, ∀ᵐ x ∂(μs N : Measure ℝ), x ∈ Ioc (0 : ℝ) B.cap)
    (hOrder : ∀ N, (B.intensityAbove b hb : Measure ℝ) ≤ (μs N : Measure ℝ))
    (hWeak : Tendsto μs atTop (𝓝 (B.intensityAbove b hb)))
    (hIndividuals : ∀ i, Tendsto (fun m => weightOrderedPaddedLaw (P m) wgt i) atTop (𝓝 (B.individuals i)))
    (hBands : ∀ N, Tendsto (fun m => weightOrderedBandResidual (P m) wgt N b) atTop (𝓝 (μs N))) :
    ∀ ε > (0 : ℝ), ∀ᶠ N in atTop, ∀ᶠ m in atTop,
      |(P m).expectedTerminalMaximum b-
        (B.prefixIntensityState N b hbH (B.intensityAbove b hb)
          (B.truncation N b hb).intensity_supported).expectedMaximum| < ε := by
  let μ := B.intensityAbove b hb
  have hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) B.cap := (B.truncation 0 b hb).intensity_supported
  let Cs := fun N => B.prefixIntensityState N b hbH μ hμ
  let Ds := fun N => B.prefixIntensityState N b hbH (μs N) (hμs N)
  have hResidual := hybrid_intensity_benchmark_difference_tendsto (fun N => N) Cs Ds μ B.cap
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hOrder hWeak
  have hResidualAbs : Tendsto (fun N => |(Ds N).expectedMaximum-(Cs N).expectedMaximum|)
      atTop (𝓝 (0 : ℝ)) := by simpa only [abs_zero] using hResidual.abs
  have hRank : Tendsto (fun N : ℕ => (B.cap : ℝ)*(1/((wgt b)^2*(N+1 : ℕ)))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (ProphetSecretary.Analysis.reciprocal_rank_tendsto_zero ((wgt b)^2)).const_mul (B.cap : ℝ)
  intro ε hε
  have hε3 : 0 < ε/3 := by positivity
  filter_upwards [(tendsto_order.mp hResidualAbs).2 (ε/3) hε3,
    (tendsto_order.mp hRank).2 (ε/3) hε3] with N hRes hSmall
  have hFiniteRaw := weightOrderedBandState_expectedMaximum_tendsto sizes P B wgt N b hbH hcap
    (μs N) (hμs N) hIndividuals (hBands N)
  have hFinite : ∀ᶠ m in atTop,
      |(weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)).expectedMaximum-
        (Ds N).expectedMaximum| < ε/3 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hFiniteRaw (ε/3) hε3
  filter_upwards [hFinite] with m hm
  have hCausal := weightOrderedBandState_benchmark_error_le (P m) wgt N B.cap b hbH (hcap m)
    hwgt0 hwgtZero (hWeight m) hbPos (fun x hx => hwgt hx.le)
  have hA := hCausal.trans_lt hSmall
  change |(P m).expectedTerminalMaximum b-(Cs N).expectedMaximum| < ε
  calc
    _ ≤ |(P m).expectedTerminalMaximum b-
        (weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)).expectedMaximum|+
        |(weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)).expectedMaximum-
          (Cs N).expectedMaximum| := abs_sub_le _ _ _
    _ ≤ |(P m).expectedTerminalMaximum b-
        (weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)).expectedMaximum|+
        (|(weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)).expectedMaximum-
            (Ds N).expectedMaximum|+|(Ds N).expectedMaximum-(Cs N).expectedMaximum|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ < ε := by linarith only [hA,hm,hRes]

end ProphetSecretary.Limiting
