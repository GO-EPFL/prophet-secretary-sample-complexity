import ProphetSecretary.Limiting.LabeledPoissonBandError
import ProphetSecretary.Limiting.LabeledResidualData
import ProphetSecretary.Limiting.HybridIntensityUniformError
import ProphetSecretary.Limiting.HybridIntensityBenchmarkLimit

/-!
# Fixed-band value and benchmark limits from structural body convergence

Causal residual Poissonization, actual fixed-prefix weak hybrid continuity,
and vanishing excess residual intensity are combined in that order. Only
source structural convergence and common cap assumptions are used.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting

theorem LabeledBandConvergence.fixed_band_two_limits {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ))
    (b W : ℝ≥0) (hb : (B.terminal : ℝ)<b) (hbH : b≤B.cap)
    (hQatom : ∀ i, (B.individuals i : Measure ℝ) {(b : ℝ)}=0) (hμatom : B.intensity {(b : ℝ)}=0) :
    (∀ ε>(0 : ℝ), ∀ᶠ N in atTop, ∀ᶠ m in atTop, ∀ w c : ℝ,
      0≤w → w≤W → 0≤c →
      |Model.optimalTerminalScalarValue (P m) b w c-
        (B.prefixIntensityState N b hbH (B.intensityAbove b hb)
          (B.truncation N b hb).intensity_supported).optimalScalarValue w c|<ε) ∧
    (∀ ε>(0 : ℝ), ∀ᶠ N in atTop, ∀ᶠ m in atTop,
      |(P m).expectedTerminalMaximum b-
        (B.prefixIntensityState N b hbH (B.intensityAbove b hb)
          (B.truncation N b hb).intensity_supported).expectedMaximum|<ε) := by
  obtain ⟨μs,hFirst,hSecond,hSupport,hOrder⟩ := h.residual_data hCap b hb hQatom hμatom
  let μ := B.intensityAbove b hb
  have hμ : ∀ᵐ x ∂(μ : Measure ℝ), x∈Ioc (0 : ℝ) B.cap := (B.truncation 0 b hb).intensity_supported
  let Cs := fun N => B.prefixIntensityState N b hbH μ hμ
  let Ds := fun N => B.prefixIntensityState N b hbH (μs N) (hSupport N)
  have hResidualV := hybrid_intensity_uniform_error (fun N => N) Cs Ds μ B.cap W
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (hμ.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) hOrder hSecond
  have hResidualM := hybrid_intensity_benchmark_difference_tendsto (fun N => N) Cs Ds μ B.cap
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hOrder hSecond
  have hResidualMAbs : Tendsto (fun N => |(Ds N).expectedMaximum-(Cs N).expectedMaximum|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [abs_zero] using hResidualM.abs
  have hJoint : ∀ ε>(0 : ℝ), ∀ᶠ N in atTop, ∀ᶠ m in atTop,
      (∀ w c : ℝ, 0≤w → w≤W → 0≤c →
        |Model.optimalTerminalScalarValue (P m) b w c-(Cs N).optimalScalarValue w c|<ε) ∧
      |(P m).expectedTerminalMaximum b-(Cs N).expectedMaximum|<ε := by
    intro ε hε
    have hε3 : 0<ε/3 := by positivity
    filter_upwards [hResidualV (ε/3) hε3,
      (tendsto_order.mp hResidualMAbs).2 (ε/3) hε3,
      h.poisson_band_error_two_limits hCap b W hb hbH (ε/3) hε3] with N hResV hResM hPoisson
    have hWeakV := labeledBandState_uniform_weak sizes P B N b W hbH hCap (μs N)
      (hSupport N) h.individual_weak (hFirst N) (ε/3) hε3
    have hWeakM := labeledBandState_expectedMaximum_tendsto sizes P B N b hbH hCap (μs N)
      (hSupport N) h.individual_weak (hFirst N)
    have hWeakMAbs : ∀ᶠ m in atTop,
        |(labeledBandState (P m) N B.cap b hbH (hCap m)).expectedMaximum-(Ds N).expectedMaximum|<ε/3 := by
      simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hWeakM (ε/3) hε3
    filter_upwards [hPoisson,hWeakV,hWeakMAbs] with m hmP hmV hmM
    constructor
    · intro w c hw hwW hc
      have h1 := hmP.1 w c hw hwW hc
      have h2 := hmV w c hw hwW hc
      have h3 := hResV w c hw hwW hc
      calc
        _ ≤ |Model.optimalTerminalScalarValue (P m) b w c-
            (labeledBandState (P m) N B.cap b hbH (hCap m)).optimalScalarValue w c|+
          |(labeledBandState (P m) N B.cap b hbH (hCap m)).optimalScalarValue w c-(Cs N).optimalScalarValue w c| := abs_sub_le _ _ _
        _ ≤ |Model.optimalTerminalScalarValue (P m) b w c-
            (labeledBandState (P m) N B.cap b hbH (hCap m)).optimalScalarValue w c|+
          (|(labeledBandState (P m) N B.cap b hbH (hCap m)).optimalScalarValue w c-(Ds N).optimalScalarValue w c|+
            |(Ds N).optimalScalarValue w c-(Cs N).optimalScalarValue w c|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
        _ < ε := by linarith only [h1,h2,h3]
    · calc
        _ ≤ |(P m).expectedTerminalMaximum b-
            (labeledBandState (P m) N B.cap b hbH (hCap m)).expectedMaximum|+
          |(labeledBandState (P m) N B.cap b hbH (hCap m)).expectedMaximum-(Cs N).expectedMaximum| := abs_sub_le _ _ _
        _ ≤ |(P m).expectedTerminalMaximum b-
            (labeledBandState (P m) N B.cap b hbH (hCap m)).expectedMaximum|+
          (|(labeledBandState (P m) N B.cap b hbH (hCap m)).expectedMaximum-(Ds N).expectedMaximum|+
            |(Ds N).expectedMaximum-(Cs N).expectedMaximum|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
        _ < ε := by linarith only [hmP.2,hmM,hResM]
  constructor
  · intro ε hε
    filter_upwards [hJoint ε hε] with N hN
    filter_upwards [hN] with m hm
    exact hm.1
  · intro ε hε
    filter_upwards [hJoint ε hε] with N hN
    filter_upwards [hN] with m hm
    exact hm.2

end ProphetSecretary.Limiting
