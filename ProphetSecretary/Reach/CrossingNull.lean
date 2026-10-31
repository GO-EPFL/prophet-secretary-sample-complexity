import ProphetSecretary.Reach.SelectionCharge
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Null arrival and endpoint equalities at continuation roots

For a fixed unseen state, its continuation root depends on offer values alone.
Actual clock replacement therefore makes equality with any arrival clock null.
Endpoint equalities occupy at most one interior scalar weight on each complete
world; measurable product integration excludes them for almost every weight.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

/-- An independent uniform arrival clock cannot equal a measurable statistic of
the complete value vector. Independence is derived by actual clock replacement. -/
lemma Instance.measure_clock_eq_valueStatistic (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (j : Fin n) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    (P.worldLaw ν) {ω : World n Seed | f ω.1 = ω.2.1 j} = 0 := by
  let E := {ω : World n Seed | f ω.1 = ω.2.1 j}
  have hE : MeasurableSet E := measurableSet_eq_fun (hf.comp measurable_fst)
    ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))
  have hrep := P.replaceClock_measurePreserving ν j
  have hpre := hE.preimage hrep.measurable
  have hinner (ω : World n Seed) :
      Instance.uniformClock (Prod.mk ω ⁻¹' ((Instance.replaceClock j) ⁻¹' E)) = 0 := by
    have he : Prod.mk ω ⁻¹' ((Instance.replaceClock j) ⁻¹' E) = {f ω.1} := by
      ext s
      simp only [E, Set.mem_preimage, Set.mem_setOf_eq, Instance.replaceClock, Function.update_self,
        Set.mem_singleton_iff]
      exact eq_comm
    rw [he]
    exact measure_singleton _
  calc
    _ = ((P.worldLaw ν).prod Instance.uniformClock) ((Instance.replaceClock j) ⁻¹' E) :=
      (hrep.measure_preimage hE.nullMeasurableSet).symm
    _ = ∫⁻ ω, Instance.uniformClock (Prod.mk ω ⁻¹' ((Instance.replaceClock j) ⁻¹' E)) ∂P.worldLaw ν :=
      Measure.prod_apply hpre
    _ = 0 := by simp only [hinner, lintegral_zero]

lemma Instance.clock_ne_valueStatistic_ae (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (j : Fin n) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, f ω.1 ≠ ω.2.1 j := by
  rw [ae_iff]
  simpa only [not_not] using P.measure_clock_eq_valueStatistic ν j f hf

lemma Instance.crossingTime_ne_clock_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (z : ℝ) (i : Fin n) (A : Finset (Fin n)) (j : Fin n) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν,
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (ω.1 i) ≠ ω.2.1 j := by
  apply P.clock_ne_valueStatistic_ae ν j (fun x =>
    (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (x i))
  exact measurable_const.sub ((((P.restrictTo A).measurable_durationRoot
    (P.restrictTo_integrable_maximum A hP)).comp (measurable_pi_apply i)).div_const z)

lemma Instance.all_crossingTimes_ne_clocks_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν] (z : ℝ) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ (i : Fin n) (A : Finset (Fin n)) (j : Fin n),
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (ω.1 i) ≠ ω.2.1 j :=
  ae_all_iff.mpr fun i => ae_all_iff.mpr fun A => ae_all_iff.mpr fun j =>
    P.crossingTime_ne_clock_ae hP ν z i A j

lemma normalizedDurationRatio_solution {d lam : ℝ} (hlam : lam ≠ 0)
    (heq : d = (1 - lam) / lam) : lam = 1 / (1 + d) := by
  have hmul := (eq_div_iff hlam).mp heq
  have h : lam * (1 + d) = 1 := by nlinarith
  have hd : 1 + d ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h
    norm_num at h
  exact (eq_div_iff hd).mpr h

/-- For a fixed world there are at most two real scalar solutions, including the
irrelevant total-division value at zero; hence at most one interior solution. -/
lemma normalizedDurationRatio_fiber_null (d : ℝ) :
    (volume.restrict (Ioo (0 : ℝ) 1)) {lam : ℝ | d = (1 - lam) / lam} = 0 := by
  have hsub : {lam : ℝ | d = (1 - lam) / lam} ⊆ ({0, 1 / (1 + d)} : Set ℝ) := by
    intro lam heq
    by_cases hlam : lam = 0
    · simp [hlam]
    · have hs := normalizedDurationRatio_solution hlam heq
      simp [hs]
  have hfinite : ({0, 1 / (1 + d)} : Set ℝ).Finite := (Set.finite_singleton _).insert 0
  exact measure_mono_null hsub (hfinite.measure_zero _)

lemma measurable_statistic_ne_ratio_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (D : Ω → ℝ) (hD : Measurable D) :
    ∀ᵐ lam ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ᵐ ω ∂μ, D ω ≠ (1 - lam) / lam := by
  have hm : MeasurableSet {v : Ω × ℝ | D v.1 ≠ (1 - v.2) / v.2} :=
    (measurableSet_eq_fun (hD.comp measurable_fst)
      ((measurable_const.sub measurable_snd).div measurable_snd)).compl
  apply (Measure.ae_ae_comm hm).mp
  exact Filter.Eventually.of_forall fun ω => by
    rw [ae_iff]
    simpa only [not_not] using normalizedDurationRatio_fiber_null (D ω)

/-- Endpoint roots at elapsed time zero occur on a null set of scalar weights,
for arbitrary offer laws, including atoms. No atom enumeration is needed. -/
lemma Instance.crossing_endpoint_null (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (i : Fin n) (A : Finset (Fin n)) :
    ∀ᵐ lam ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ᵐ ω : World n Seed ∂P.worldLaw ν,
      (P.restrictTo A).durationRoot (P.restrictTo_integrable_maximum A hP) (ω.1 i) ≠ (1 - lam) / lam := by
  apply measurable_statistic_ne_ratio_ae (P.worldLaw ν) _
  exact ((P.restrictTo A).measurable_durationRoot (P.restrictTo_integrable_maximum A hP)).comp
    ((measurable_pi_apply i).comp measurable_fst)

lemma Instance.all_crossing_endpoints_null (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ lam ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ᵐ ω : World n Seed ∂P.worldLaw ν,
      ∀ (i : Fin n) (A : Finset (Fin n)),
        (P.restrictTo A).durationRoot (P.restrictTo_integrable_maximum A hP) (ω.1 i) ≠ (1 - lam) / lam := by
  have h := ae_all_iff.mpr fun i => ae_all_iff.mpr fun A => P.crossing_endpoint_null hP ν i A
  filter_upwards [h] with lam hlam
  exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun A => hlam i A

/-- Simultaneous regularity for the finite boundary calculation: every branch
root avoids all arrival clocks, and every branch avoids the elapsed-time-zero
endpoint, for almost every normalized scalar weight and almost every world. -/
lemma Instance.crossing_regular_data_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ lam ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ᵐ ω : World n Seed ∂P.worldLaw ν,
      (∀ (i : Fin n) (A : Finset (Fin n)),
        (P.restrictTo A).durationRoot (P.restrictTo_integrable_maximum A hP) (ω.1 i) ≠ (1 - lam) / lam) ∧
      (∀ (i : Fin n) (A : Finset (Fin n)) (j : Fin n),
        (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) ((1 - lam) / lam) (ω.1 i) ≠ ω.2.1 j) := by
  filter_upwards [P.all_crossing_endpoints_null hP ν] with lam hlam
  filter_upwards [hlam, P.all_crossingTimes_ne_clocks_ae hP ν ((1 - lam) / lam)] with ω he hc
  exact ⟨he, hc⟩

lemma Instance.crossingTime_ne_zero_of_root_ne (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z x : ℝ} (hz : z ≠ 0)
    (hd : P.durationRoot hP x ≠ z) : P.crossingTime hP z x ≠ 0 := by
  intro heq
  unfold Instance.crossingTime at heq
  have hdiv : P.durationRoot hP x / z = 1 := by linarith
  have he := (div_eq_iff hz).mp hdiv
  exact hd (by simpa only [one_mul] using he)

lemma Instance.all_crossingTimes_ne_zero_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ lam ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ᵐ ω : World n Seed ∂P.worldLaw ν,
      ∀ (i : Fin n) (A : Finset (Fin n)),
        (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) ((1 - lam) / lam) (ω.1 i) ≠ 0 := by
  filter_upwards [P.all_crossing_endpoints_null hP ν, ae_restrict_mem measurableSet_Ioo] with lam he hlam
  have hz : 0 < (1 - lam) / lam := div_pos (sub_pos.mpr hlam.2) hlam.1
  filter_upwards [he] with ω hω
  intro i A
  exact (P.restrictTo A).crossingTime_ne_zero_of_root_ne (P.restrictTo_integrable_maximum A hP) hz.ne' (hω i A)

end ProphetSecretary.Model
