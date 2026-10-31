import ProphetSecretary.Limiting.HybridIndividualClock

/-!
# Individual-offer compensation in a hybrid process

The exact finite-clock rate identity remains valid while a policy may also stop
at anonymous arrivals. It is derived from replacement of the retained clock and
pending survival of the same rule, including every observed individual zero.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def HybridRule.individualReachedPremium (π : HybridRule n Seed) (i : Fin n)
    (g : ℝ × HybridWorld n Seed → ℝ≥0∞) (v : HybridWorld n Seed) : ℝ≥0∞ :=
  if v.2.2.1 i ≤ π.realizedDuration v then g (v.2.2.1 i, eraseIndividualClock i v) else 0

noncomputable def HybridRule.individualStoppedHazard (π : HybridRule n Seed) (i : Fin n)
    (g : ℝ × HybridWorld n Seed → ℝ≥0∞) (q : HybridWorld n Seed × ℝ) : ℝ≥0∞ :=
  if q.2 ≤ π.realizedDuration q.1 ∧ q.2 < q.1.2.2.1 i
    then g (q.2, eraseIndividualClock i q.1) / ENNReal.ofReal (1 - q.2) else 0

lemma HybridRule.measurable_individualReachedPremium (π : HybridRule n Seed) (hπ : π.IsMeasurable) (i : Fin n)
    (g : ℝ × HybridWorld n Seed → ℝ≥0∞) (hg : Measurable g) : Measurable (π.individualReachedPremium i g) := by
  have hui : Measurable (fun v : HybridWorld n Seed => v.2.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  exact Measurable.ite (measurableSet_le hui (π.measurable_realizedDuration hπ))
    (hg.comp (hui.prodMk (measurable_eraseIndividualClock i))) measurable_const

lemma HybridRule.measurable_individualStoppedHazard (π : HybridRule n Seed) (hπ : π.IsMeasurable) (i : Fin n)
    (g : ℝ × HybridWorld n Seed → ℝ≥0∞) (hg : Measurable g) : Measurable (π.individualStoppedHazard i g) := by
  have hui : Measurable (fun q : HybridWorld n Seed × ℝ => q.1.2.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  exact Measurable.ite ((measurableSet_le measurable_snd ((π.measurable_realizedDuration hπ).comp measurable_fst)).inter
    (measurableSet_lt measurable_snd hui))
    ((hg.comp (measurable_snd.prodMk ((measurable_eraseIndividualClock i).comp measurable_fst))).div
      (measurable_const.sub measurable_snd).ennreal_ofReal) measurable_const

omit [MeasurableSpace Seed] in
lemma HybridRule.individualReachedPremium_replace (π : HybridRule n Seed) (i : Fin n)
    (g : ℝ × HybridWorld n Seed → ℝ≥0∞) (z : HybridWorld n Seed × ℝ) (hu : z.2 ≤ 1) :
    π.individualReachedPremium i g (replaceIndividualClock i z) =
      if z.2 ≤ π.pendingIndividualTime i z.1 then g (z.2, eraseIndividualClock i z.1) else 0 := by
  have he := π.reach_replaceIndividualClock i z hu
  unfold HybridRule.individualReachedPremium
  rw [eraseIndividualClock_replace]
  simp only [replaceIndividualClock, Model.Instance.replaceClock, Function.update_self]
  exact ite_congr (propext he) (fun _ => rfl) (fun _ => rfl)

omit [MeasurableSpace Seed] in
lemma HybridRule.individualStoppedHazard_replace (π : HybridRule n Seed) (i : Fin n)
    (g : ℝ × HybridWorld n Seed → ℝ≥0∞) (z : HybridWorld n Seed × ℝ) (t : ℝ) (ht : t ≤ 1) :
    π.individualStoppedHazard i g (replaceIndividualClock i z, t) =
      Probability.uniformHazardKernel (fun s => g (s, eraseIndividualClock i z.1))
        (π.pendingIndividualTime i z.1) (z.2, t) := by
  by_cases htu : t < z.2
  · have he := π.survival_replaceIndividualClock i z t ht htu.le
    unfold HybridRule.individualStoppedHazard Probability.uniformHazardKernel
    rw [eraseIndividualClock_replace]
    simp only [replaceIndividualClock, Model.Instance.replaceClock, Function.update_self, htu, and_true]
    exact ite_congr (propext he) (fun _ => rfl) (fun _ => rfl)
  · simp [HybridRule.individualStoppedHazard, Probability.uniformHazardKernel,
      replaceIndividualClock, Model.Instance.replaceClock, htu]

lemma HybridRule.lintegral_individualReachedPremium (π : HybridRule n Seed) (hπ : π.IsMeasurable) (i : Fin n)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : ℝ × HybridWorld n Seed → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ v, π.individualReachedPremium i g v ∂hybridWorldLaw P μ ν) =
      ∫⁻ v, ∫⁻ t, if t ≤ π.pendingIndividualTime i v then g (t, eraseIndividualClock i v) else 0
        ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ ν := by
  have hmp := replaceIndividualClock_measurePreserving P μ ν i
  have hm := π.measurable_individualReachedPremium hπ i g hg
  have hcomp : Measurable (fun z : HybridWorld n Seed × ℝ => π.individualReachedPremium i g (replaceIndividualClock i z)) :=
    hm.comp hmp.measurable
  rw [← hmp.lintegral_comp hm, lintegral_prod _ hcomp.aemeasurable]
  apply lintegral_congr
  intro v
  apply lintegral_congr_ae
  filter_upwards [Probability.uniformClock_mem_open_unit] with t ht
  exact π.individualReachedPremium_replace i g (v, t) ht.2.le

lemma HybridRule.lintegral_individualStoppedHazard (π : HybridRule n Seed) (hπ : π.IsMeasurable) (i : Fin n)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : ℝ × HybridWorld n Seed → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ v, ∫⁻ t, π.individualStoppedHazard i g (v, t) ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ ν) =
      ∫⁻ v, ∫⁻ t, if t ≤ π.pendingIndividualTime i v then g (t, eraseIndividualClock i v) else 0
        ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ ν := by
  let f : HybridWorld n Seed → ℝ≥0∞ := fun v => ∫⁻ t, π.individualStoppedHazard i g (v, t) ∂Model.Instance.uniformClock
  have hm : Measurable f := (π.measurable_individualStoppedHazard hπ i g hg).lintegral_prod_right'
  have hmp := replaceIndividualClock_measurePreserving P μ ν i
  have hcomp : Measurable (fun z : HybridWorld n Seed × ℝ => f (replaceIndividualClock i z)) := hm.comp hmp.measurable
  change (∫⁻ v, f v ∂hybridWorldLaw P μ ν) = _
  rw [← hmp.lintegral_comp hm, lintegral_prod _ hcomp.aemeasurable]
  apply lintegral_congr
  intro v
  calc
    _ = ∫⁻ u, ∫⁻ t, Probability.uniformHazardKernel (fun s => g (s, eraseIndividualClock i v))
        (π.pendingIndividualTime i v) (u, t) ∂Model.Instance.uniformClock ∂Model.Instance.uniformClock := by
      apply lintegral_congr
      intro u
      apply lintegral_congr_ae
      filter_upwards [Probability.uniformClock_mem_open_unit] with t ht
      exact π.individualStoppedHazard_replace i g (v, u) t ht.2.le
    _ = _ := Probability.lintegral_uniform_hazard _ (hg.comp (measurable_id.prodMk measurable_const)) _

/-- Actual retained-offer compensator for the common hybrid policy. -/
theorem HybridRule.individual_compensator (π : HybridRule n Seed) (hπ : π.IsMeasurable) (i : Fin n)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : ℝ × HybridWorld n Seed → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ v, π.individualReachedPremium i g v ∂hybridWorldLaw P μ ν) =
      ∫⁻ v, ∫⁻ t, π.individualStoppedHazard i g (v, t) ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ ν :=
  (π.lintegral_individualReachedPremium hπ i P μ ν g hg).trans
    (π.lintegral_individualStoppedHazard hπ i P μ ν g hg).symm

end ProphetSecretary.Limiting
