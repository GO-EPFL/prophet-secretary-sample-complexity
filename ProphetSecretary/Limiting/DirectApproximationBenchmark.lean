import ProphetSecretary.Limiting.RareDesignBenchmark
import ProphetSecretary.Limiting.CountableBenchmarkLimit
import ProphetSecretary.Limiting.TruncatedScoreLimits
import ProphetSecretary.Probability.BoundedCDFOrder

/-!
# Direct benchmarks with a prescribed virtual count

The virtual count is an external schedule, so it may be kept unchanged
under a likelihood perturbation. At each positive level the cutoff eventually
leaves the intensity tail unchanged. The Bernoulli void probability tends
to the Poisson void probability; bounded layer cake then gives the actual
benchmark limit. No policy or score convergence is inferred from this step.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal Topology BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

lemma rareDesign_cdf_gap_eq {n : ℕ} (P : Model.Instance n) (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x∈Icc (0 : ℝ) H)
    (k : ℕ) (hk : 0<k) (hm : μ.mass≤(k : ℝ≥0)) {t : ℝ} (ht : 0≤t) :
    (hybridValueLaw P μ).real {v | hybridMaximum 0 v≤t}-
      (rareDesign P μ H hμ k hk hm).valuesLaw.real {v | Model.Instance.maximum v≤t}=
      P.valuesLaw.real {v | Model.Instance.maximum v≤t}*
        (Real.exp (-(μ : Measure ℝ).real (Ioi t))-
          (1-(k : ℝ)⁻¹*(μ : Measure ℝ).real (Ioi t))^k) := by
  rw [hybridMaximum_real_Iic _ _ ht ht,rareDesign_maximum_real_Iic _ _ _ _ _ _ _ ht,
    finite_maximum_real_Iic _ ht]
  ring

namespace CountableInstance

noncomputable def finiteDirectApproximationAt (B : CountableInstance) (N : ℕ) (cut : ℝ)
    (hcut : (B.terminal : ℝ)<cut) (k : ℕ) (hk : 0<k)
    (hm : (B.intensityAbove cut hcut).mass≤(k : ℝ≥0)) : Model.Instance (N+k) :=
  let C := B.truncation N cut hcut
  rareDesign C.individuals C.intensity C.cap
    (C.intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) k hk hm

lemma finiteDirectApproximationAt_bounded (B : CountableInstance) (N : ℕ) (cut : ℝ)
    (hcut : (B.terminal : ℝ)<cut) (k : ℕ) (hk : 0<k)
    (hm : (B.intensityAbove cut hcut).mass≤(k : ℝ≥0)) :
    ∀ i, ∀ᵐ x ∂(B.finiteDirectApproximationAt N cut hcut k hk hm).law i, x≤(B.cap : ℝ) :=
  rareDesign_bounded (B.truncation N cut hcut).individuals (B.intensityAbove cut hcut) B.cap
    (B.truncation N cut hcut).individual_bounded
    ((B.truncation N cut hcut).intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) k hk hm

lemma finiteDirectApproximationAt_cdf_gap_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (Ns ks : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal : ℝ)<bs m)
    (hk : ∀ m, 0<ks m) (hm : ∀ m, (B.intensityAbove (bs m) (hbs m)).mass≤(ks m : ℝ≥0))
    (hCut : Tendsto bs atTop (𝓝 (B.terminal : ℝ))) (hK : Tendsto ks atTop atTop)
    {t : ℝ} (ht : 0<t) :
    Tendsto (fun m =>
      (hybridValueLaw (B.individualPrefix (Ns m)) (B.intensityAbove (bs m) (hbs m))).real
        {v | hybridMaximum 0 v≤t}-
      (B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)).valuesLaw.real
        {v | Model.Instance.maximum v≤t}) atTop (𝓝 (0 : ℝ)) := by
  let q := B.intensity.real (Ioi t)
  have hRaw := (Real.tendsto_one_add_div_pow_exp (-q)).comp hK
  have hPow : Tendsto (fun m => (1-(ks m : ℝ)⁻¹*q)^(ks m)) atTop (𝓝 (Real.exp (-q))) := by
    convert hRaw using 1
    funext m
    congr 1
    ring
  have hError : Tendsto (fun m => |Real.exp (-q)-(1-(ks m : ℝ)⁻¹*q)^(ks m)|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,abs_zero] using (hPow.const_sub (Real.exp (-q))).abs
  have htAbove : (B.terminal : ℝ)<t := by simpa only [hZero,NNReal.coe_zero] using ht
  have hBelow := hCut.eventually (gt_mem_nhds htAbove)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hBelow,hError.eventually (gt_mem_nhds hε)] with m hBelowM hSmall
  let C := B.truncation (Ns m) (bs m) (hbs m)
  have hTail : (C.intensity : Measure ℝ).real (Ioi t)=q :=
    B.intensityAbove_real_upper (hbs m) t hBelowM.le
  have hGap := rareDesign_cdf_gap_eq C.individuals C.intensity C.cap
    (C.intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) (ks m) (hk m) (hm m) ht.le
  rw [hTail] at hGap
  rw [Real.dist_eq,sub_zero]
  change |(hybridValueLaw C.individuals C.intensity).real {v | hybridMaximum 0 v≤t}-
    (rareDesign C.individuals C.intensity C.cap
      (C.intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) (ks m) (hk m) (hm m)).valuesLaw.real
      {v | Model.Instance.maximum v≤t}|<ε
  rw [hGap,abs_mul,abs_of_nonneg measureReal_nonneg]
  exact (mul_le_of_le_one_left (abs_nonneg _) measureReal_le_one).trans_lt hSmall

/-- Prescribed-count direct designs have the actual prophet limit. The same
count schedule can therefore be used for every law in a perturbation family. -/
theorem finiteDirectApproximationAt_expectedMaximum_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (Ns ks : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal : ℝ)<bs m)
    (hk : ∀ m, 0<ks m) (hm : ∀ m, (B.intensityAbove (bs m) (hbs m)).mass≤(ks m : ℝ≥0))
    (hN : Tendsto Ns atTop atTop) (hCut : Tendsto bs atTop (𝓝 (B.terminal : ℝ)))
    (hK : Tendsto ks atTop atTop) :
    Tendsto (fun m => (B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)).expectedMaximum)
      atTop (𝓝 B.expectedMaximum) := by
  let C := fun m => B.truncation (Ns m) (bs m) (hbs m)
  let Q := fun m => B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
  let g := fun m t => (hybridValueLaw (C m).individuals (C m).intensity).real {v | hybridMaximum 0 v≤t}-
    (Q m).valuesLaw.real {v | Model.Instance.maximum v≤t}
  have hMeas (m : ℕ) : Measurable (g m) := by
    have hC : Monotone (fun t : ℝ => (hybridValueLaw (C m).individuals (C m).intensity).real {v | hybridMaximum 0 v≤t}) :=
      fun _ _ h => measureReal_mono (fun _ hv => hv.trans h)
    have hQ : Monotone (fun t : ℝ => (Q m).valuesLaw.real {v | Model.Instance.maximum v≤t}) :=
      fun _ _ h => measureReal_mono (fun _ hv => hv.trans h)
    exact hC.measurable.sub hQ.measurable
  have hBound (m : ℕ) : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) B.cap), ‖g m t‖≤1 := by
    apply Eventually.of_forall
    intro t
    dsimp only [g]
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith only [show (0 : ℝ)≤(hybridValueLaw (C m).individuals (C m).intensity).real {v | hybridMaximum 0 v≤t} from measureReal_nonneg,
      show (hybridValueLaw (C m).individuals (C m).intensity).real {v | hybridMaximum 0 v≤t}≤1 from measureReal_le_one,
      show (0 : ℝ)≤(Q m).valuesLaw.real {v | Model.Instance.maximum v≤t} from measureReal_nonneg,
      show (Q m).valuesLaw.real {v | Model.Instance.maximum v≤t}≤1 from measureReal_le_one]
  have hLimit : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) B.cap), Tendsto (fun m => g m t) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact B.finiteDirectApproximationAt_cdf_gap_tendsto hZero Ns ks bs hbs hk hm hCut hK ht.1
  have hDCT := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
    (Eventually.of_forall (fun m => (hMeas m).aestronglyMeasurable.restrict))
    (Eventually.of_forall hBound) (integrable_const _) hLimit
  simp only [integral_zero] at hDCT
  have hQR (m : ℕ) : ∀ᵐ x ∂(Q m).valuesLaw, Model.Instance.maximum x∈Icc (0 : ℝ) B.cap := by
    have hValues : ∀ᵐ x ∂(Q m).valuesLaw, ∀ i, x i≤(B.cap : ℝ) :=
      ae_all_iff.mpr (fun i => (measurePreserving_eval (Q m).law i).quasiMeasurePreserving.ae
        (B.finiteDirectApproximationAt_bounded (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m) i))
    exact hValues.mono (fun x hx => ⟨Model.Instance.maximum_nonnegative x,Model.Instance.maximum_le x B.cap.property hx⟩)
  have hCR (m : ℕ) : ∀ᵐ v ∂hybridValueLaw (C m).individuals (C m).intensity,
      hybridMaximum 0 v∈Icc (0 : ℝ) B.cap := by
    filter_upwards [hybridValueLaw_values_bounds (C m).individuals (C m).intensity
      (C m).individual_bounded (C m).intensity_supported] with v hv
    exact ⟨hybridMaximum_nonnegative _ _,hybridMaximum_le B.cap.property B.cap.property v (fun i => (hv i).2)⟩
  have hMean (m : ℕ) : (Q m).expectedMaximum-(C m).expectedMaximum=∫ t in Ioc (0 : ℝ) B.cap, g m t := by
    change (∫ x, Model.Instance.maximum x ∂(Q m).valuesLaw)-
      (∫ v, hybridMaximum (C m).terminal v ∂hybridValueLaw (C m).individuals (C m).intensity)=_
    rw [show (C m).terminal=0 from hZero,NNReal.coe_zero,
      integral_eq_bounded_strict_layercake (Q m).valuesLaw Model.Instance.measurable_maximum B.cap (hQR m),
      integral_eq_bounded_strict_layercake (hybridValueLaw (C m).individuals (C m).intensity) (measurable_hybridMaximum 0) B.cap (hCR m),
      ←integral_sub (integrable_tail_on_bounded_interval (Q m).valuesLaw Model.Instance.maximum B.cap)
        (integrable_tail_on_bounded_interval (hybridValueLaw (C m).individuals (C m).intensity) (hybridMaximum 0) B.cap)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by
      dsimp only [g]
      rw [probReal_gt_eq_one_sub_le (Q m).valuesLaw Model.Instance.measurable_maximum,
        probReal_gt_eq_one_sub_le (hybridValueLaw (C m).individuals (C m).intensity) (measurable_hybridMaximum 0)]
      ring)
  have hDiff : Tendsto (fun m => (Q m).expectedMaximum-(C m).expectedMaximum) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hMean] using hDCT
  have hHybrid := B.truncation_expectedMaximum_tendsto Ns bs hbs hN hCut
  simpa only [Q,C,sub_add_cancel,zero_add] using hDiff.add hHybrid

/-- Quantitative scalar comparison at one prescribed count, before taking
any limit. The bound is independent of the retained dimension and c. -/
lemma finiteDirectApproximationAt_value_error (B : CountableInstance) (hZero : B.terminal=0)
    (N : ℕ) (cut : ℝ) (hcut : (B.terminal : ℝ)<cut) (k : ℕ) (hk : 0<k)
    (hm : (B.intensityAbove cut hcut).mass≤(k : ℝ≥0)) {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    |Model.optimalScalarValue (B.finiteDirectApproximationAt N cut hcut k hk hm) w c-
      (B.truncation N cut hcut).optimalScalarValue w c|≤
      w*(B.cap : ℝ)*(((B.intensityAbove cut hcut).mass : ℝ)^2/(k : ℝ)+
        (Real.pi/2)*Real.sqrt (((B.intensityAbove cut hcut).mass : ℝ)^2/(k : ℝ))) :=
  (B.truncation N cut hcut).rareDesign_value_uniform_error hZero ⟨w,hw⟩
    (B.intensityAbove cut hcut).mass le_rfl k hk hm hw le_rfl hc

/-- The value limit applies to the same prescribed count under perturbation,
provided its explicit squared-intensity/count error tends to zero. -/
theorem finiteDirectApproximationAt_value_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (Ns ks : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal : ℝ)<bs m)
    (hk : ∀ m, 0<ks m) (hm : ∀ m, (B.intensityAbove (bs m) (hbs m)).mass≤(ks m : ℝ≥0))
    (hN : Tendsto Ns atTop atTop) (hCut : Tendsto bs atTop (𝓝 (B.terminal : ℝ)))
    (hSquare : Tendsto (fun m => ((B.intensityAbove (bs m) (hbs m)).mass : ℝ)^2/(ks m : ℝ))
      atTop (𝓝 (0 : ℝ))) {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    Tendsto (fun m => Model.optimalScalarValue
      (B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)) w c)
      atTop (𝓝 (B.optimalScalarValue w c)) := by
  let e := fun m => ((B.intensityAbove (bs m) (hbs m)).mass : ℝ)^2/(ks m : ℝ)
  have hSqrt : Tendsto (fun m => Real.sqrt (e m)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hSquare
  have hSmall : Tendsto (fun m => w*(B.cap : ℝ)*(e m+(Real.pi/2)*Real.sqrt (e m))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero,add_zero] using (hSquare.add (hSqrt.const_mul (Real.pi/2))).const_mul (w*(B.cap : ℝ))
  have hHybrid := B.truncation_value_tendsto Ns bs hbs hN hCut hw hc
  have hTail : Tendsto (fun m => |(B.truncation (Ns m) (bs m) (hbs m)).optimalScalarValue w c-
      B.optimalScalarValue w c|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,abs_zero] using (hHybrid.sub_const (B.optimalScalarValue w c)).abs
  have hUpper := hSmall.add hTail
  rw [zero_add] at hUpper
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hUpper
  intro m
  rw [Real.norm_eq_abs]
  exact (abs_sub_le _ _ _).trans (add_le_add
    (B.finiteDirectApproximationAt_value_error hZero (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m) hw hc) le_rfl)

end CountableInstance
end ProphetSecretary.Limiting
