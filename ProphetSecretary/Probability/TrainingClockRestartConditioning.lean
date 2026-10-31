import ProphetSecretary.Probability.CensoredClockConditioning

/-!
# Averaging independent training at a clock-history restart

The observation consists only of elapsed clock information. The actual
conditional expectation refreshes all independent training data and only
pending clocks. This differs from holding training fixed when controlling
later value errors; it supplies the averaging needed for localized restart
moments at entrances determined solely by true laws and arrival clocks.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Probability

variable {n : ℕ} {D : Type*} [mD : MeasurableSpace D]

abbrev observedClockSigma (D : Type*) [MeasurableSpace D] (n : ℕ) (t : ℝ) :
    MeasurableSpace (D × (Fin n → ℝ)) :=
  (inferInstance : MeasurableSpace (Fin n → ℝ)).comap (fun q => censorClocks t q.2)

noncomputable def restartTrainingClocks (t : ℝ)
    (q : (D × (Fin n → ℝ)) × (D × (Fin n → ℝ))) : D × (Fin n → ℝ) :=
  (q.2.1, refreshClocks t (q.1.2,q.2.2))

lemma restartTrainingClocks_measurePreserving (ν : Measure D) [IsProbabilityMeasure ν]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    MeasurePreserving (restartTrainingClocks t)
      ((ν.prod (Model.Instance.clocksLaw n)).prod (ν.prod (Model.Instance.clocksLaw n)))
      (ν.prod (Model.Instance.clocksLaw n)) := by
  let κ := Model.Instance.clocksLaw n
  have h1 : MeasurePreserving (fun q : (D × (Fin n → ℝ)) × (D × (Fin n → ℝ)) => (q.1.2,q.2))
      ((ν.prod κ).prod (ν.prod κ)) (κ.prod (ν.prod κ)) :=
    (measurePreserving_snd (μ := ν) (ν := κ)).prod (MeasurePreserving.id _)
  have h2 := (measurePreserving_prodAssoc κ ν κ).symm MeasurableEquiv.prodAssoc
  have h3 := (Measure.measurePreserving_swap (μ := κ) (ν := ν)).prod (MeasurePreserving.id κ)
  have h4 := measurePreserving_prodAssoc ν κ κ
  have h5 := (MeasurePreserving.id ν).prod (refreshClocks_measurePreserving (n := n) ht0 ht1)
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- The restart kernel is the actual CE after observing the elapsed clocks,
with the independent training array averaged rather than revealed. -/
theorem condExp_observedClockHistory (ν : Measure D) [IsProbabilityMeasure ν]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {f : D × (Fin n → ℝ) → ℝ}
    (hfm : Measurable f) (hf : Integrable f (ν.prod (Model.Instance.clocksLaw n))) :
    (ν.prod (Model.Instance.clocksLaw n))[f | observedClockSigma D n t] =ᵐ[ν.prod (Model.Instance.clocksLaw n)]
      (fun q => ∫ r, f (restartTrainingClocks t (q,r)) ∂ν.prod (Model.Instance.clocksLaw n)) := by
  let μ := ν.prod (Model.Instance.clocksLaw n)
  let C : D × (Fin n → ℝ) → (Fin n → ℝ) := fun q => censorClocks t q.2
  let R : (Fin n → ℝ) × (D × (Fin n → ℝ)) → D × (Fin n → ℝ) :=
    fun z => (z.2.1, refreshClocks t (z.1,z.2.2))
  have hCm : Measurable C := (measurable_censorClocks t).comp measurable_snd
  have hRm : Measurable R := (measurable_fst.comp measurable_snd).prodMk
    ((measurable_refreshClocks t).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hPres : MeasurePreserving (fun q : (D × (Fin n → ℝ)) × (D × (Fin n → ℝ)) => R (C q.1,q.2))
      (μ.prod μ) μ := by
    convert restartTrainingClocks_measurePreserving (n := n) ν ht0 ht1 using 1
    funext q
    exact congrArg (q.2.1, ·) (refreshClocks_censored_input t q.1.2 q.2.2)
  have hv : MeasurePreserving (fun q : (D × (Fin n → ℝ)) × (D × (Fin n → ℝ)) => q.2.2)
      (μ.prod μ) (Model.Instance.clocksLaw n) :=
    (measurePreserving_snd (μ := ν) (ν := Model.Instance.clocksLaw n)).comp measurePreserving_snd
  have hObs : ∀ᵐ q : (D × (Fin n → ℝ)) × (D × (Fin n → ℝ)) ∂μ.prod μ,
      C (R (C q.1,q.2)) = C q.1 := by
    filter_upwards [hv.quasiMeasurePreserving.ae (Model.Instance.clocks_mem_unitInterval (n := n))] with q hq
    change censorClocks t (refreshClocks t (censorClocks t q.1.2,q.2.2)) = censorClocks t q.1.2
    rw [refreshClocks_censored_input]
    exact censor_refreshClocks ht1.le q.1.2 q.2.2 (fun i => (hq i).1)
  have h := condExp_stationaryResampling μ μ hCm hRm hPres hObs hfm hf
  simpa only [C, R, observedClockSigma, restartTrainingClocks, refreshClocks_censored_input] using h

end ProphetSecretary.Probability
