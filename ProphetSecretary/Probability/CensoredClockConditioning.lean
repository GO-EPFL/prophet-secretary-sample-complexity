import ProphetSecretary.Probability.CensoredClocks
import ProphetSecretary.Probability.StationaryResampling

/-!
# Conditional fresh clocks while keeping training data fixed

The observed projection keeps arbitrary independent data and every elapsed clock
observation. The actual conditional expectation is obtained by resampling only
pending clocks. All measure-preservation and observation-invariance obligations
are proved from the independent uniform product law.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Probability

variable {n : ℕ}

lemma refreshClocks_censored_input (t : ℝ) (u v : Fin n → ℝ) :
    refreshClocks t (censorClocks t u, v) = refreshClocks t (u, v) := by
  funext i
  by_cases hi : u i < t
  · simp only [refreshClocks, refreshClock, censorClocks, min_eq_left hi.le, hi, ite_true]
  · simp only [refreshClocks, refreshClock, censorClocks, min_eq_right (le_of_not_gt hi),
      lt_self_iff_false, ite_false, hi]

variable {D : Type*} [mD : MeasurableSpace D]

abbrev dataClockHistorySigma (D : Type*) [MeasurableSpace D] (n : ℕ) (t : ℝ) :
    MeasurableSpace (D × (Fin n → ℝ)) :=
  (inferInstance : MeasurableSpace (D × (Fin n → ℝ))).comap (fun q => (q.1, censorClocks t q.2))

lemma measurable_dataClockHistory (t : ℝ) :
    Measurable (fun q : D × (Fin n → ℝ) => (q.1, censorClocks t q.2)) :=
  measurable_fst.prodMk ((measurable_censorClocks t).comp measurable_snd)

lemma dataClockHistorySigma_le (t : ℝ) : dataClockHistorySigma D n t ≤
    (inferInstance : MeasurableSpace (D × (Fin n → ℝ))) := (measurable_dataClockHistory t).comap_le

lemma dataClockHistorySigma_mono {s t : ℝ} (hst : s ≤ t) :
    dataClockHistorySigma D n s ≤ dataClockHistorySigma D n t := by
  have ht : @Measurable (D × (Fin n → ℝ)) (D × (Fin n → ℝ)) (dataClockHistorySigma D n t)
      (inferInstance : MeasurableSpace (D × (Fin n → ℝ))) (fun q => (q.1, censorClocks t q.2)) :=
    Measurable.of_comap_le le_rfl
  have h := (measurable_dataClockHistory s).comp ht
  have hs : @Measurable (D × (Fin n → ℝ)) (D × (Fin n → ℝ)) (dataClockHistorySigma D n t)
      (inferInstance : MeasurableSpace (D × (Fin n → ℝ))) (fun q => (q.1, censorClocks s q.2)) := by
    convert h using 1
    funext q
    exact congrArg (q.1, ·) (censorClocks_comp hst q.2).symm
  exact hs.comap_le

def dataClockHistoryFiltration (D : Type*) [MeasurableSpace D] (n : ℕ) :
    Filtration ℝ (inferInstance : MeasurableSpace (D × (Fin n → ℝ))) where
  seq t := dataClockHistorySigma D n t
  mono' _ _ h := dataClockHistorySigma_mono h
  le' t := dataClockHistorySigma_le t

noncomputable def resampleDataClocks (t : ℝ) (q : (D × (Fin n → ℝ)) × (Fin n → ℝ)) : D × (Fin n → ℝ) :=
  (q.1.1, refreshClocks t (q.1.2, q.2))

lemma measurable_resampleDataClocks (t : ℝ) : Measurable (@resampleDataClocks n D t) :=
  (measurable_fst.comp measurable_fst).prodMk ((measurable_refreshClocks t).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

lemma resampleDataClocks_measurePreserving (ν : Measure D) [IsProbabilityMeasure ν]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    MeasurePreserving (resampleDataClocks t)
      ((ν.prod (Model.Instance.clocksLaw n)).prod (Model.Instance.clocksLaw n))
      (ν.prod (Model.Instance.clocksLaw n)) :=
  ((MeasurePreserving.id ν).prod (refreshClocks_measurePreserving ht0 ht1)).comp
    (measurePreserving_prodAssoc ν (Model.Instance.clocksLaw n) (Model.Instance.clocksLaw n))

/-- The actual clock-history conditional expectation, with all independent data
retained. Fresh randomness is supplied only to clocks still pending at time `t`. -/
theorem condExp_dataClockHistory (ν : Measure D) [IsProbabilityMeasure ν]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {f : D × (Fin n → ℝ) → ℝ}
    (hfm : Measurable f) (hf : Integrable f (ν.prod (Model.Instance.clocksLaw n))) :
    (ν.prod (Model.Instance.clocksLaw n))[f | dataClockHistorySigma D n t] =ᵐ[ν.prod (Model.Instance.clocksLaw n)]
      (fun q => ∫ v, f (resampleDataClocks t (q, v)) ∂Model.Instance.clocksLaw n) := by
  let C : D × (Fin n → ℝ) → D × (Fin n → ℝ) := fun q => (q.1, censorClocks t q.2)
  let R : (D × (Fin n → ℝ)) × (Fin n → ℝ) → D × (Fin n → ℝ) := resampleDataClocks t
  have hPres : MeasurePreserving (fun q : (D × (Fin n → ℝ)) × (Fin n → ℝ) => R (C q.1, q.2))
      ((ν.prod (Model.Instance.clocksLaw n)).prod (Model.Instance.clocksLaw n))
      (ν.prod (Model.Instance.clocksLaw n)) := by
    convert resampleDataClocks_measurePreserving (n := n) ν ht0 ht1 using 1
    funext q
    exact congrArg (q.1.1, ·) (refreshClocks_censored_input t q.1.2 q.2)
  have hv : MeasurePreserving (Prod.snd : (D × (Fin n → ℝ)) × (Fin n → ℝ) → (Fin n → ℝ))
      ((ν.prod (Model.Instance.clocksLaw n)).prod (Model.Instance.clocksLaw n))
      (Model.Instance.clocksLaw n) := measurePreserving_snd
  have hObs : ∀ᵐ q : (D × (Fin n → ℝ)) × (Fin n → ℝ)
      ∂(ν.prod (Model.Instance.clocksLaw n)).prod (Model.Instance.clocksLaw n), C (R (C q.1, q.2)) = C q.1 := by
    filter_upwards [hv.quasiMeasurePreserving.ae (Model.Instance.clocks_mem_unitInterval (n := n))] with q hq
    change (q.1.1, censorClocks t (refreshClocks t (censorClocks t q.1.2, q.2))) =
      (q.1.1, censorClocks t q.1.2)
    rw [refreshClocks_censored_input]
    exact congrArg (q.1.1, ·) (censor_refreshClocks ht1.le q.1.2 q.2 (fun i => (hq i).1))
  have h := condExp_stationaryResampling (ν.prod (Model.Instance.clocksLaw n)) (Model.Instance.clocksLaw n)
    (measurable_dataClockHistory t) (measurable_resampleDataClocks t) hPres hObs hfm hf
  simpa only [C, R, resampleDataClocks, refreshClocks_censored_input] using h

end ProphetSecretary.Probability
