import ProphetSecretary.Probability.Hoeffding.FirstProjection

/-!
# Almost-surely bounded kernels and their actual conditional projections

A measurable kernel bounded only on its actual product law is replaced by a
symmetric clipping equal to it almost surely. Actual coordinate conditional
means preserve AE equality. Consequently its original first projections are
centered and bounded AE, with the same score identity as a globally bounded
representative. No bound on impossible offer vectors is required.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Probability.Hoeffding

noncomputable def boundedRepresentative {Ω : Type*} (C : ℝ≥0) (f : Ω → ℝ) (x : Ω) : ℝ :=
  max (-(C : ℝ)) (min (C : ℝ) (f x))

lemma measurable_boundedRepresentative {Ω : Type*} [MeasurableSpace Ω] (C : ℝ≥0)
    {f : Ω → ℝ} (hf : Measurable f) : Measurable (boundedRepresentative C f) :=
  measurable_const.max (measurable_const.min hf)
lemma boundedRepresentative_abs_le {Ω : Type*} (C : ℝ≥0) (f : Ω → ℝ) (x : Ω) :
    |boundedRepresentative C f x| ≤ C := by
  rw [abs_le]
  exact ⟨le_max_left _ _,max_le (by linarith [C.coe_nonneg]) (min_le_left _ _)⟩
lemma boundedRepresentative_eq_of_abs_le {Ω : Type*} (C : ℝ≥0) (f : Ω → ℝ) {x : Ω}
    (hx : |f x| ≤ C) : boundedRepresentative C f x = f x := by
  simp only [boundedRepresentative,min_eq_right (abs_le.mp hx).2,max_eq_right (abs_le.mp hx).1]
lemma boundedRepresentative_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (C : ℝ≥0) {f : Ω → ℝ} (hb : ∀ᵐ x ∂μ, |f x| ≤ C) : boundedRepresentative C f =ᵐ[μ] f :=
  hb.mono fun _ hx => boundedRepresentative_eq_of_abs_le C f hx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma firstProjection_congr_ae (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f g : (ι → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g) (hfg : f =ᵐ[Measure.pi μ] g) (i : ι) :
    firstProjection μ f i =ᵐ[μ i] firstProjection μ g i := by
  have hc := component_congr_ae μ {i} hfg
  have hfull : (fun x : ι → ℝ => firstProjection μ f i (x i)) =ᵐ[Measure.pi μ]
      (fun x => firstProjection μ g i (x i)) := by
    filter_upwards [hc] with x hx
    rw [firstProjection_eq_component,firstProjection_eq_component]
    exact hx
  have hp := measurePreserving_eval μ i
  have hset : MeasurableSet {a | firstProjection μ f i a = firstProjection μ g i a} :=
    measurableSet_eq_fun (measurable_firstProjection μ hf i) (measurable_firstProjection μ hg i)
  have h := (ae_map_iff hp.measurable.aemeasurable hset).mpr hfull
  rw [hp.map_eq] at h
  exact h

lemma firstProjection_abs_le_ae (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (i : ι) :
    ∀ᵐ a ∂μ i, |firstProjection μ f i a| ≤ 2*(C : ℝ) := by
  have he := firstProjection_congr_ae μ (measurable_boundedRepresentative C hf) hf (boundedRepresentative_ae_eq C hb) i
  filter_upwards [he] with a ha
  rw [← ha]
  exact firstProjection_abs_le μ C (boundedRepresentative_abs_le C f) i a

lemma integral_firstProjection_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (i : ι) :
    (∫ a, firstProjection μ f i a ∂μ i) = 0 := by
  have he := firstProjection_congr_ae μ (measurable_boundedRepresentative C hf) hf (boundedRepresentative_ae_eq C hb) i
  exact (integral_congr_ae he.symm).trans
    (integral_firstProjection μ (measurable_boundedRepresentative C hf) C (boundedRepresentative_abs_le C f) i)

lemma memLp_firstProjection_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (i : ι) (p : ENNReal) :
    MemLp (firstProjection μ f i) p (μ i) := by
  apply MemLp.of_bound (measurable_firstProjection μ hf i).aestronglyMeasurable (2*(C : ℝ))
  exact (firstProjection_abs_le_ae μ hf C hb i).mono fun a ha => by simpa only [Real.norm_eq_abs] using ha

lemma integral_kernel_firstProjection_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (i : ι) :
    (∫ x, f x*firstProjection μ f i (x i) ∂Measure.pi μ) = ∫ a, firstProjection μ f i a^2 ∂μ i := by
  let g := boundedRepresentative C f
  have hgm : Measurable g := measurable_boundedRepresentative C hf
  have he : g =ᵐ[Measure.pi μ] f := boundedRepresentative_ae_eq C hb
  have hgi := firstProjection_congr_ae μ hgm hf he i
  have hfull := (measurePreserving_eval μ i).quasiMeasurePreserving.ae hgi
  calc
    _ = ∫ x, g x*firstProjection μ g i (x i) ∂Measure.pi μ := by
      apply integral_congr_ae
      filter_upwards [he,hfull] with x hx hi
      rw [hx,hi]
    _ = ∫ a, firstProjection μ g i a^2 ∂μ i := integral_kernel_firstProjection μ hgm C (boundedRepresentative_abs_le C f) i
    _ = _ := integral_congr_ae (hgi.mono fun a ha => congrArg (fun v : ℝ => v^2) ha)

end ProphetSecretary.Probability.Hoeffding
