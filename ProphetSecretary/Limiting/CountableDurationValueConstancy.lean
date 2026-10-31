import ProphetSecretary.Limiting.CountableConditionalDurationScore
import ProphetSecretary.Limiting.CountableDurationValueContinuity
import ProphetSecretary.Probability.AntitoneKernelConstancy

/-!
# Individual-value constancy of canonical duration

In the zero-response alternative of `lem:nonzero`, the actual canonical
duration is constant throughout the convex hull of one marginal's support,
on a single conull event. Continuity of its conditional mean supplies the
support endpoints; monotonicity then fills their whole interval. The mean
belongs to that interval, so substitution of the mean preserves duration.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance

theorem canonical_durationAtValue_ae_constant_on_support_hull
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()),
      ∀ x ∈ convexHull ℝ (B.individuals i : Measure ℝ).support,
        (B.valueRule w c).durationAtValue i (v,x)=(B.valueRule w c).realizedDuration v := by
  let π := B.valueRule w c
  have hπ : π.IsMeasurable := B.valueRule_isMeasurable hw.le hc.le
  obtain ⟨a,b,ha,hb,hConst⟩ :=
    ProphetSecretary.Probability.antitone_kernel_ae_constant_on_support_hull
      (B.completeWorldLaw (Measure.dirac ())) (B.individuals i : Measure ℝ) B.cap
      (B.individual_supported i) (fun x v => π.durationAtValue i (v,x))
      (π.integrable_durationAtValue_fixed hπ B (Measure.dirac ()) i)
      (B.canonical_duration_antitone_candidateValue hw.le i)
      (B.canonical_conditionalDurationAtValue_continuous hZero hw hc i)
      (B.canonical_conditionalDurationAtValue_ae_constant_of_zero_scores hw hc i hScores)
  have hXi : MeasurePreserving (fun v : CompleteWorld Unit => v.2.1 i)
      (B.completeWorldLaw (Measure.dirac ())) (B.individuals i : Measure ℝ) :=
    (B.individualValue_measurePreserving i).comp (measurePreserving_fst.comp measurePreserving_snd)
  have hSupp : ∀ᵐ x ∂(B.individuals i : Measure ℝ), x ∈ (B.individuals i : Measure ℝ).support :=
    (B.individuals i : Measure ℝ).support_mem_ae
  have hHull := ProphetSecretary.Probability.convexHull_eq_Icc_of_extrema ha hb
  filter_upwards [hConst,hXi.quasiMeasurePreserving.ae hSupp] with v hv hX x hx
  rw [hHull] at hx
  have hXab : v.2.1 i ∈ Icc a b := ⟨ha.2 hX,hb.2 hX⟩
  exact (hv x hx).trans ((hv (v.2.1 i) hXab).symm.trans (π.durationAtValue_self i v))

lemma integrable_individualValue (B : CountableInstance) (i : ℕ) :
    Integrable id (B.individuals i : Measure ℝ) := by
  apply Integrable.of_bound measurable_id.aestronglyMeasurable (B.cap : ℝ)
  filter_upwards [B.individual_supported i] with x hx
  change ‖x‖ ≤ (B.cap : ℝ)
  rw [Real.norm_eq_abs,abs_of_nonneg hx.1]
  exact hx.2

lemma individual_mean_mem_support_hull (B : CountableInstance) (i : ℕ) :
    (∫ x, x ∂(B.individuals i : Measure ℝ)) ∈ convexHull ℝ (B.individuals i : Measure ℝ).support := by
  obtain ⟨a,b,ha,hb⟩ := ProphetSecretary.Probability.bounded_probability_support_extrema
    (B.individuals i : Measure ℝ) B.cap (B.individual_supported i)
  rw [ProphetSecretary.Probability.convexHull_eq_Icc_of_extrema ha hb]
  exact ProphetSecretary.Probability.mean_mem_Icc_of_support_extrema _ (B.integrable_individualValue i) ha hb

theorem canonical_durationAtValue_mean_ae_eq
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (fun v => (B.valueRule w c).durationAtValue i (v,∫ x, x ∂(B.individuals i : Measure ℝ)))
      =ᵐ[B.completeWorldLaw (Measure.dirac ())] (B.valueRule w c).realizedDuration := by
  filter_upwards [B.canonical_durationAtValue_ae_constant_on_support_hull hZero hw hc i hScores] with v hv
  exact hv _ (B.individual_mean_mem_support_hull i)

lemma durationAtValue_replaceIndividualValue {Seed : Type*} (π : CountableRule Seed)
    (i : ℕ) (v : CompleteWorld Seed) (x y : ℝ) :
    π.durationAtValue i (replaceIndividualValue i (v,y),x)=π.durationAtValue i (v,x) := by
  simp only [CountableRule.durationAtValue,replaceIndividualValue,Function.update_idem]

end ProphetSecretary.Limiting.CountableInstance
