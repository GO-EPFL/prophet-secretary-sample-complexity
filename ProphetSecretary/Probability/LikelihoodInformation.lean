import ProphetSecretary.Probability.LikelihoodTilt
import ProphetSecretary.Model.Learner
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym

/-!
# Information bounds for bounded likelihood tilts

The score information is kept as the explicit sum of marginal second moments. Bounds
on likelihood ratios may depend on the finite reservoir size only to establish
integrability; the divergence estimates retain dimension-free constants.
-/

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal BigOperators

namespace ProphetSecretary.Probability

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma klFun_le_sq_sub_one {r : ℝ} (hr : 0 ≤ r) : klFun r ≤ (r - 1) ^ 2 := by
  by_cases h0 : r = 0
  · simp [h0, klFun_zero]
  · have hp := lt_of_le_of_ne hr (Ne.symm h0)
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hp) hr
    unfold klFun
    nlinarith

lemma klDiv_withDensity_ofReal_le_chiSquare (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → ℝ) (hr : Measurable r) (h0 : ∀ᵐ x ∂μ, 0 ≤ r x)
    [IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (r x)))] :
    klDiv (μ.withDensity (fun x => ENNReal.ofReal (r x))) μ ≤
      ∫⁻ x, ENNReal.ofReal ((r x - 1) ^ 2) ∂μ := by
  rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous μ _)]
  apply lintegral_mono_ae
  filter_upwards [Measure.rnDeriv_withDensity μ hr.ennreal_ofReal, h0] with x hx hpos
  rw [hx, ENNReal.toReal_ofReal hpos]
  exact ENNReal.ofReal_le_ofReal (klFun_le_sq_sub_one hpos)

noncomputable def oppositeTiltRatio (h : Ω → ℝ) (t : ℝ) (x : Ω) : ℝ :=
  tiltFactor h t x / tiltFactor h (-t) x

lemma measurable_oppositeTiltRatio {h : Ω → ℝ} (hh : Measurable h) (t : ℝ) :
    Measurable (oppositeTiltRatio h t) := (measurable_tiltFactor hh t).div (measurable_tiltFactor hh (-t))

lemma oppositeTiltRatio_nonnegative {μ : Measure Ω} {h : Ω → ℝ}
    (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) {t : ℝ} (ht : |t| ≤ 1 / 4) :
    ∀ᵐ x ∂μ, 0 ≤ oppositeTiltRatio h t x := by
  have hneg : |-t| ≤ 1 / 4 := by simpa only [abs_neg] using ht
  filter_upwards [tiltFactor_ae_nonnegative hb ht, tiltFactor_ae_nonnegative hb hneg] with x hp hm
  exact div_nonneg hp hm

lemma tiltLaw_opposite_withDensity {μ : Measure Ω} {h : Ω → ℝ} (hh : Measurable h)
    (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) {t : ℝ} (ht : |t| ≤ 1 / 4) :
    tiltLaw μ h t = (tiltLaw μ h (-t)).withDensity (fun x => ENNReal.ofReal (oppositeTiltRatio h t x)) := by
  rw [tiltLaw, tiltLaw, ← withDensity_mul μ (measurable_tiltFactor hh (-t) |>.ennreal_ofReal)
    (measurable_oppositeTiltRatio hh t |>.ennreal_ofReal)]
  apply withDensity_congr_ae
  have hneg : |-t| ≤ 1 / 4 := by simpa only [abs_neg] using ht
  filter_upwards [hb] with x hx
  have hm : 0 < tiltFactor h (-t) x := by
    have hlow : (3 / 4 : ℝ) ≤ tiltFactor h (-t) x := (tiltFactor_bounds hneg hx).1
    linarith
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul hm.le]
  unfold oppositeTiltRatio
  congr 1
  field_simp

lemma oppositeTiltRatio_chiSquare_bound {a t : ℝ} (ha : |a| ≤ 1) (ht : |t| ≤ 1 / 4) :
    (1 - t * a) * (((1 + t * a) / (1 - t * a)) - 1) ^ 2 ≤ 8 * t ^ 2 * a ^ 2 := by
  have hneg : |-t| ≤ 1 / 4 := by simpa only [abs_neg] using ht
  have hlow : (1 / 2 : ℝ) ≤ 1 - t * a := by
    have h := (tiltFactor_bounds hneg ha).1
    linarith
  have hp : 0 < 1 - t * a := by linarith
  have he : (1 - t * a) * (((1 + t * a) / (1 - t * a)) - 1) ^ 2 =
      (4 * t ^ 2 * a ^ 2) / (1 - t * a) := by
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ hp).mpr
  have hm := mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg a)) (sub_nonneg.mpr hlow)
  nlinarith

/-- Opposite marginal tilts have relative entropy at most `8t² E[h²]`. -/
lemma tiltLaw_klDiv_le (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) (hm : ∫ x, h x ∂μ = 0)
    {t : ℝ} (ht : |t| ≤ 1 / 4) :
    klDiv (tiltLaw μ h t) (tiltLaw μ h (-t)) ≤ ENNReal.ofReal (8 * t ^ 2 * ∫ x, h x ^ 2 ∂μ) := by
  have hneg : |-t| ≤ 1 / 4 := by simpa only [abs_neg] using ht
  haveI := tiltLaw_probability hh hb hm ht
  haveI := tiltLaw_probability hh hb hm hneg
  let r := oppositeTiltRatio h t
  have hr : Measurable r := measurable_oppositeTiltRatio hh t
  have h0 : ∀ᵐ x ∂tiltLaw μ h (-t), 0 ≤ r x :=
    (tiltLaw_absolutelyContinuous μ h (-t)).ae_le (oppositeTiltRatio_nonnegative hb ht)
  have heq := tiltLaw_opposite_withDensity hh hb ht
  haveI : IsProbabilityMeasure ((tiltLaw μ h (-t)).withDensity (fun x => ENNReal.ofReal (r x))) := by
    rw [← heq]
    infer_instance
  have hKL := klDiv_withDensity_ofReal_le_chiSquare (tiltLaw μ h (-t)) r hr h0
  rw [← heq] at hKL
  have hchi : Measurable (fun x => ENNReal.ofReal ((r x - 1) ^ 2)) := by fun_prop
  have hi2 : Integrable (fun x => h x ^ 2) μ := integrable_pow_of_bound hh zero_le_one hb 2
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ((r x - 1) ^ 2) ∂tiltLaw μ h (-t) := hKL
    _ = ∫⁻ x, ENNReal.ofReal (tiltFactor h (-t) x * (r x - 1) ^ 2) ∂μ := by
      rw [tiltLaw, lintegral_withDensity_eq_lintegral_mul μ
        (measurable_tiltFactor hh (-t) |>.ennreal_ofReal) hchi]
      apply lintegral_congr_ae
      filter_upwards [tiltFactor_ae_nonnegative hb hneg] with x hx
      rw [Pi.mul_apply, ← ENNReal.ofReal_mul hx]
    _ ≤ ∫⁻ x, ENNReal.ofReal (8 * t ^ 2 * h x ^ 2) ∂μ := by
      apply lintegral_mono_ae
      exact hb.mono fun x hx => ENNReal.ofReal_le_ofReal (by
        simpa only [r, oppositeTiltRatio, tiltFactor, neg_mul, sub_eq_add_neg] using oppositeTiltRatio_chiSquare_bound hx ht)
    _ = ENNReal.ofReal (8 * t ^ 2 * ∫ x, h x ^ 2 ∂μ) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hi2.const_mul (8 * t ^ 2))
        (Filter.Eventually.of_forall fun x => by positivity), integral_const_mul]

lemma tiltLaw_symmetric_klDiv_le (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) (hm : ∫ x, h x ∂μ = 0)
    {t : ℝ} (ht : |t| ≤ 1 / 4) :
    klDiv (tiltLaw μ h t) (tiltLaw μ h (-t)) + klDiv (tiltLaw μ h (-t)) (tiltLaw μ h t) ≤
      ENNReal.ofReal (16 * t ^ 2 * ∫ x, h x ^ 2 ∂μ) := by
  have hplus := tiltLaw_klDiv_le μ h hh hb hm ht
  have hminus := tiltLaw_klDiv_le μ h hh hb hm (by simpa only [abs_neg] using ht : |-t| ≤ 1 / 4)
  simp only [neg_neg, neg_sq] at hminus
  have hsum := add_le_add hplus hminus
  have hnonneg : 0 ≤ 8 * t ^ 2 * ∫ x, h x ^ 2 ∂μ := by positivity
  rw [← ENNReal.ofReal_add hnonneg hnonneg] at hsum
  have he : 8 * t ^ 2 * (∫ x, h x ^ 2 ∂μ) + 8 * t ^ 2 * (∫ x, h x ^ 2 ∂μ) =
      16 * t ^ 2 * (∫ x, h x ^ 2 ∂μ) := by ring
  simpa only [he] using hsum

/-- Data processing for relative entropy under an arbitrary measurable observation.
The proof uses the actual mapped-Radon–Nikodym conditional expectation identity and
conditional Jensen; neither source nor target needs a standard Borel hypothesis. -/
lemma klDiv_map_le {Υ : Type*} [mΥ : MeasurableSpace Υ] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (T : Ω → Υ) (hT : Measurable T) :
    klDiv (μ.map T) (ν.map T) ≤ klDiv μ ν := by
  by_cases htop : klDiv μ ν = ∞
  · simp [htop]
  have hac := (klDiv_ne_top_iff.mp htop).1
  have hllr := (klDiv_ne_top_iff.mp htop).2
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  haveI : IsProbabilityMeasure (ν.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  have hm : MeasurableSpace.comap T mΥ ≤ mΩ := hT.comap_le
  haveI : SigmaFinite (ν.trim hm) := inferInstance
  let R : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal
  let r : Υ → ℝ := fun y => ((μ.map T).rnDeriv (ν.map T) y).toReal
  have hRi : Integrable R ν := Measure.integrable_toReal_rnDeriv
  have hφi : Integrable (fun x => klFun (R x)) ν := (integrable_klFun_rnDeriv_iff hac).mpr hllr
  have hrm : Measurable (fun y => klFun (r y)) := measurable_klFun.comp (Measure.measurable_rnDeriv (μ.map T) (ν.map T)).ennreal_toReal
  have hRN := toReal_rnDeriv_map hac hT
  have hJ := ConvexOn.map_condExp_le hm convexOn_klFun (continuous_klFun.lowerSemicontinuous.lowerSemicontinuousOn (Ici 0))
    (Filter.Eventually.of_forall fun x => (ENNReal.toReal_nonneg : 0 ≤ R x)) isClosed_Ici hRi hφi
  have hCEi : Integrable (ν[(fun x => klFun (R x)) | MeasurableSpace.comap T mΥ]) ν := integrable_condExp
  have hleft : (fun x => klFun (r (T x))) ≤ᵐ[ν] ν[(fun x => klFun (R x)) | MeasurableSpace.comap T mΥ] := by
    filter_upwards [hRN, hJ] with x hx hJx
    change r (T x) = ν[R | MeasurableSpace.comap T mΥ] x at hx
    rw [hx]
    exact hJx
  have hpull : Integrable (fun x => klFun (r (T x))) ν := by
    apply hCEi.abs.mono' (hrm.comp hT).aestronglyMeasurable
    filter_upwards [hleft] with x hx
    simp only [Real.norm_eq_abs, Function.comp_apply]
    rw [abs_of_nonneg (klFun_nonneg (show 0 ≤ r (T x) from ENNReal.toReal_nonneg))]
    exact hx.trans (le_abs_self _)
  have hmp : MeasurePreserving T ν (ν.map T) := ⟨hT, rfl⟩
  have hmapInt : Integrable (fun y => klFun (r y)) (ν.map T) :=
    (hmp.integrable_comp hrm.aestronglyMeasurable).mp hpull
  have hint := integral_mono_ae hpull hCEi hleft
  rw [integral_condExp hm] at hint
  have heq := integral_map (μ := ν) hT.aemeasurable hrm.aestronglyMeasurable
  rw [klDiv_eq_lintegral_klFun_of_ac (hac.map hT), klDiv_eq_lintegral_klFun_of_ac hac]
  rw [← ofReal_integral_eq_lintegral_ofReal hmapInt (Filter.Eventually.of_forall fun _ => klFun_nonneg ENNReal.toReal_nonneg),
    ← ofReal_integral_eq_lintegral_ofReal hφi (Filter.Eventually.of_forall fun _ => klFun_nonneg ENNReal.toReal_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  rw [heq]
  exact hint

lemma klDiv_map_measurableEquiv {Υ : Type*} [MeasurableSpace Υ] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (e : Ω ≃ᵐ Υ) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  haveI : IsProbabilityMeasure (μ.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  haveI : IsProbabilityMeasure (ν.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  apply le_antisymm (klDiv_map_le μ ν e e.measurable)
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm e.symm.measurable
  simpa only [MeasurableEquiv.map_symm_map] using h

lemma klDiv_prod_swap {Υ : Type*} [MeasurableSpace Υ] (μ ν : Measure Ω) (ρ σ : Measure Υ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] :
    klDiv (ρ.prod μ) (σ.prod ν) = klDiv (μ.prod ρ) (ν.prod σ) := by
  have h := klDiv_map_measurableEquiv (μ.prod ρ) (ν.prod σ) MeasurableEquiv.prodComm
  change klDiv ((μ.prod ρ).map Prod.swap) ((ν.prod σ).map Prod.swap) = _ at h
  rw [(Measure.measurePreserving_swap (μ := μ) (ν := ρ)).map_eq,
    (Measure.measurePreserving_swap (μ := ν) (ν := σ)).map_eq] at h
  exact h

/-- Exact additivity for independent product experiments, including arbitrary independent seeds. -/
lemma klDiv_prod {Υ : Type*} [MeasurableSpace Υ] (μ ν : Measure Ω) (ρ σ : Measure Υ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] :
    klDiv (μ.prod ρ) (ν.prod σ) = klDiv μ ν + klDiv ρ σ := by
  have hc := InformationTheory.klDiv_compProd_eq_add (μ := μ) (ν := ν)
    (κ := Kernel.const Ω ρ) (η := Kernel.const Ω σ)
  simp only [Measure.compProd_const] at hc
  have hs := InformationTheory.klDiv_compProd_left (μ := ρ) (ν := σ) (κ := Kernel.const Υ μ)
  simp only [Measure.compProd_const] at hs
  rw [← klDiv_prod_swap μ μ ρ σ, hs] at hc
  exact hc

/-- Exact finite-product aggregation. Its proof uses measurable-equivalence invariance
and the actual library chain rule, rather than assuming tensorization. -/
lemma klDiv_pi (n : ℕ) (μ ν : Fin n → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  induction n with
  | zero =>
    let x : Fin 0 → Ω := fun i => Fin.elim0 i
    rw [Measure.pi_of_empty μ x, Measure.pi_of_empty ν x, klDiv_self]
    simp
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0
    have he := klDiv_map_measurableEquiv (Measure.pi μ) (Measure.pi ν) e
    rw [(measurePreserving_piFinSuccAbove μ 0).map_eq,
      (measurePreserving_piFinSuccAbove ν 0).map_eq] at he
    rw [← he, klDiv_prod, ih]
    simp only [Fin.zero_succAbove, Fin.sum_univ_succ]

lemma productTiltLaw_klDiv_le {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    {t : ℝ} (ht : |t| ≤ 1 / 4) :
    klDiv (productTiltLaw μ h t) (productTiltLaw μ h (-t)) ≤ ENNReal.ofReal (8 * t ^ 2 * information μ h) := by
  have hneg : |-t| ≤ 1 / 4 := by simpa only [abs_neg] using ht
  haveI : ∀ i, IsProbabilityMeasure (tiltLaw (μ i) (h i) t) := fun i => tiltLaw_probability (hh i) (hb i) (hm i) ht
  haveI : ∀ i, IsProbabilityMeasure (tiltLaw (μ i) (h i) (-t)) := fun i => tiltLaw_probability (hh i) (hb i) (hm i) hneg
  unfold productTiltLaw
  rw [klDiv_pi]
  calc
    _ ≤ ∑ i, ENNReal.ofReal (8 * t ^ 2 * ∫ x, h i x ^ 2 ∂μ i) :=
      Finset.sum_le_sum fun i _ => tiltLaw_klDiv_le (μ i) (h i) (hh i) (hb i) (hm i) ht
    _ = ENNReal.ofReal (∑ i, 8 * t ^ 2 * ∫ x, h i x ^ 2 ∂μ i) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)).symm
    _ = _ := by rw [information, Finset.mul_sum]

end ProphetSecretary.Probability

namespace ProphetSecretary.Model.Instance

open ProphetSecretary.Probability

variable {n : ℕ}

/-- Exact KL cost of a full independent hard-budget reservoir. -/
lemma reservoirLaw_klDiv (P Q : Instance n) (k : ℕ) :
    klDiv (P.reservoirLaw k) (Q.reservoirLaw k) = (k : ℝ≥0∞) * klDiv P.valuesLaw Q.valuesLaw := by
  change klDiv (Measure.pi (fun i => Measure.pi (fun _ : Fin k => P.law i)))
    (Measure.pi (fun i => Measure.pi (fun _ : Fin k => Q.law i))) =
      (k : ℝ≥0∞) * klDiv (Measure.pi P.law) (Measure.pi Q.law)
  rw [klDiv_pi, klDiv_pi]
  simp_rw [klDiv_pi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]

lemma reservoir_tilt_klDiv_le (P : Instance n) (k : ℕ) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) {t : ℝ} (ht : |t| ≤ 1 / 4) :
    klDiv ((P.likelihoodTilt h hh hb hm t ht).reservoirLaw k)
      ((P.likelihoodTilt h hh hb hm (-t) (by simpa only [abs_neg] using ht)).reservoirLaw k) ≤
        ENNReal.ofReal (8 * (k : ℝ) * t ^ 2 * information P.law h) := by
  rw [reservoirLaw_klDiv]
  have hKL := productTiltLaw_klDiv_le P.law h hh hb hm ht
  calc
    _ ≤ (k : ℝ≥0∞) * ENNReal.ofReal (8 * t ^ 2 * information P.law h) := mul_le_mul le_rfl hKL bot_le bot_le
    _ = ENNReal.ofReal ((k : ℝ) * (8 * t ^ 2 * information P.law h)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg k)]
      simp
    _ = _ := by congr 1; ring

end ProphetSecretary.Model.Instance

namespace ProphetSecretary.Model.Learner

open ProphetSecretary.Probability

variable {n k : ℕ}

/-- The learner sees its auxiliary seed and the adaptively collected transcript.
The same measurable map is used for every instance law. -/
noncomputable def transcriptLaw (L : Learner n k) (P : Instance n) : Measure (L.Seed × Transcript n) :=
  ((P.reservoirLaw k).prod L.seedLaw).map (fun z : Reservoir n k × L.Seed =>
    (z.2, trainingTranscript L.request z.2 z.1))

lemma measurable_trainingObservation (L : Learner n k) :
    Measurable (fun z : Reservoir n k × L.Seed => (z.2, trainingTranscript L.request z.2 z.1)) :=
  measurable_snd.prodMk (measurable_trainingTranscript L.request L.measurable_request measurable_snd measurable_fst)

instance transcriptLaw_probability (L : Learner n k) (P : Instance n) : IsProbabilityMeasure (L.transcriptLaw P) :=
  Measure.isProbabilityMeasure_map L.measurable_trainingObservation.aemeasurable

/-- Adaptive training is a measurable observation of the finite independent reservoir.
This proves the information bound from the executor model; no adaptive chain rule is assumed. -/
lemma transcript_klDiv_le_reservoir (L : Learner n k) (P Q : Instance n) :
    klDiv (L.transcriptLaw P) (L.transcriptLaw Q) ≤ (k : ℝ≥0∞) * klDiv P.valuesLaw Q.valuesLaw := by
  have h := klDiv_map_le ((P.reservoirLaw k).prod L.seedLaw) ((Q.reservoirLaw k).prod L.seedLaw)
    _ L.measurable_trainingObservation
  rw [klDiv_prod, klDiv_self, add_zero, Instance.reservoirLaw_klDiv] at h
  exact h

lemma transcript_tilt_klDiv_le (L : Learner n k) (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) {t : ℝ} (ht : |t| ≤ 1 / 4) :
    klDiv (L.transcriptLaw (P.likelihoodTilt h hh hb hm t ht))
      (L.transcriptLaw (P.likelihoodTilt h hh hb hm (-t) (by simpa only [abs_neg] using ht))) ≤
        ENNReal.ofReal (8 * (k : ℝ) * t ^ 2 * information P.law h) := by
  have hobs := klDiv_map_le
    (((P.likelihoodTilt h hh hb hm t ht).reservoirLaw k).prod L.seedLaw)
    (((P.likelihoodTilt h hh hb hm (-t) (by simpa only [abs_neg] using ht)).reservoirLaw k).prod L.seedLaw)
    _ L.measurable_trainingObservation
  rw [klDiv_prod, klDiv_self, add_zero] at hobs
  exact hobs.trans (P.reservoir_tilt_klDiv_le k h hh hb hm ht)

/-- Sum of the two transcript relative entropies, with a hard per-distribution budget. -/
lemma symmetric_transcript_tilt_klDiv_le (L : Learner n k) (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) {t : ℝ} (ht : |t| ≤ 1 / 4) :
    klDiv (L.transcriptLaw (P.likelihoodTilt h hh hb hm t ht))
      (L.transcriptLaw (P.likelihoodTilt h hh hb hm (-t) (by simpa only [abs_neg] using ht))) +
    klDiv (L.transcriptLaw (P.likelihoodTilt h hh hb hm (-t) (by simpa only [abs_neg] using ht)))
      (L.transcriptLaw (P.likelihoodTilt h hh hb hm t ht)) ≤
        ENNReal.ofReal (16 * (k : ℝ) * t ^ 2 * information P.law h) := by
  have hp := L.transcript_tilt_klDiv_le P h hh hb hm ht
  have hn := L.transcript_tilt_klDiv_le P h hh hb hm (by simpa only [abs_neg] using ht : |-t| ≤ 1 / 4)
  simp only [neg_neg, neg_sq] at hn
  have hs := add_le_add hp hn
  have hnonneg : 0 ≤ 8 * (k : ℝ) * t ^ 2 * information P.law h :=
    mul_nonneg (by positivity) (information_nonnegative P.law h)
  rw [← ENNReal.ofReal_add hnonneg hnonneg] at hs
  have he : 8 * (k : ℝ) * t ^ 2 * information P.law h + 8 * (k : ℝ) * t ^ 2 * information P.law h =
      16 * (k : ℝ) * t ^ 2 * information P.law h := by ring
  simpa only [he] using hs

end ProphetSecretary.Model.Learner

