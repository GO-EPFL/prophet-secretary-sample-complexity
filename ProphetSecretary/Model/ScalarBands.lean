import ProphetSecretary.Model.ScalarSupport
import ProphetSecretary.Analysis.ThresholdBand
import ProphetSecretary.Model.ClockReplacement
import ProphetSecretary.Model.BellmanPerformance

/-!
# Actual finite acceptance bands

Keep a candidate's clock free while fixing all other clocks. The child's unseen
set shrinks with elapsed time. Fixed-policy horizon support and the actual finite
duration lower bound show that the acceptance gap grows at a uniform positive
rate on this path, including across identity-removal jumps.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def otherUnseen (u : Fin n → ℝ) (i : Fin n) (t : ℝ) : Finset (Fin n) :=
  (Finset.univ.erase i).filter (fun j ↦ t ≤ u j)

lemma otherUnseen_antitone (u : Fin n → ℝ) (i : Fin n) : Antitone (otherUnseen u i) := by
  intro t s hts j hj
  obtain ⟨hjA, hjs⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨hjA, hts.trans hjs⟩

lemma otherUnseen_not_mem (u : Fin n → ℝ) (i : Fin n) (t : ℝ) : i ∉ otherUnseen u i t := by
  simp [otherUnseen]

lemma measurable_otherUnseen (u : Fin n → ℝ) (i : Fin n) : Measurable (otherUnseen u i) := by
  rw [measurable_finset_iff]
  intro j
  apply measurableSet_setOf.mp
  by_cases hji : j = i
  · subst j
    simp only [otherUnseen, Finset.mem_filter, Finset.mem_erase, ne_eq, not_true_eq_false,
      Finset.mem_univ, and_true, false_and, setOf_false]
    exact MeasurableSet.empty
  · simp only [otherUnseen, Finset.mem_filter, Finset.mem_erase, hji, not_false_eq_true,
      Finset.mem_univ, ne_eq, and_self, true_and]
    change MeasurableSet (Iic (u j))
    exact measurableSet_Iic

/-- With the candidate's own clock replaced by `t`, the child set depends on
exactly the other identities that have not arrived strictly before `t`. -/
lemma unseen_replaceClock_erase (x u : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    (unseen (history Finset.univ x (Function.update u i t) t)).erase i = otherUnseen u i t := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [otherUnseen]
  · simp [unseen, history, otherUnseen, hji, not_lt]

lemma Instance.measurable_stateElapsedValue (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Measurable (fun z : Finset (Fin n) × ℝ ↦ P.continuationValue z.1 (max 0 (1 - z.2)) w c) := by
  apply measurable_from_prod_countable_right
  intro A
  exact ((optimalScalarValue_durationWeight_continuousOn (P.restrictTo A)
    (P.restrictTo_integrable_maximum A hP) hw).comp_continuous
      (continuous_const.mul (continuous_const.max (continuous_const.sub continuous_id)))
      (fun _t ↦ mul_nonneg hc (le_max_left _ _))).measurable

noncomputable def Instance.candidateGap (P : Instance n) (w c : ℝ) (i : Fin n)
    (x : ℝ) (u : Fin n → ℝ) (t : ℝ) : ℝ :=
  w * x - P.continuationValue (otherUnseen u i t) (max 0 (1 - t)) w c

lemma Instance.measurable_candidateGap (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (i : Fin n) (x : ℝ) (u : Fin n → ℝ) : Measurable (P.candidateGap w c i x u) := by
  have hmap : Measurable (fun t : ℝ ↦ (otherUnseen u i t, t)) :=
    (measurable_otherUnseen u i).prodMk measurable_id
  have hv := (P.measurable_stateElapsedValue hP hw hc).comp hmap
  have hg := (measurable_const (a := w * x)).sub hv
  convert hg using 1
  funext t
  rfl


/-- This is a statement about increasing elapsed time. It is derived from strong
increase in remaining horizon, with the sign reversed, plus option-set monotonicity. -/
theorem Instance.candidateGap_slope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (x : ℝ) (u : Fin n → ℝ) :
    ProphetSecretary.Analysis.SlopeLowerBoundOn (P.candidateGap w c i x u)
      (c / (4 * (1 + (n : ℝ)))) (Icc (0 : ℝ) 1) := by
  intro t ht s hs hts
  have hset := otherUnseen_antitone u i hts
  have hg := P.continuationValue_growth hP (otherUnseen u i t) hw hc
    (sub_nonneg.mpr hs.2) (sub_le_sub_left hts 1)
  have hm := P.optimalScalarValue_restrictTo_mono hP hset hw.le
    (mul_nonneg hc (sub_nonneg.mpr hs.2))
  have he : (1 - t) - (1 - s) = s - t := by ring
  rw [he] at hg
  change P.continuationValue (otherUnseen u i s) (1 - s) w c ≤
    P.continuationValue (otherUnseen u i t) (1 - s) w c at hm
  unfold Instance.candidateGap
  rw [max_eq_right (sub_nonneg.mpr ht.2), max_eq_right (sub_nonneg.mpr hs.2)]
  linarith

/-- The actual clock-integrated acceptance-band bound has no unproved
anti-concentration hypothesis. Constants are explicit and may depend on finite n. -/
theorem Instance.candidateGap_band_volume (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c δ : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hδ : 0 ≤ δ) (i : Fin n) (x : ℝ) (u : Fin n → ℝ) :
    volume.real (ProphetSecretary.Analysis.thresholdBand (P.candidateGap w c i x u) δ) ≤
      2 * δ / (c / (4 * (1 + (n : ℝ)))) := by
  exact ProphetSecretary.Analysis.volumeReal_thresholdBand_le (by positivity) hδ
    (P.candidateGap_slope hP hw hc.le i x u)

lemma Instance.candidateGap_eq_replacedAcceptanceGap (P : Instance n) (w c : ℝ)
    (i : Fin n) (x u : Fin n → ℝ) (t : ℝ) :
    P.candidateGap w c i (x i) u t =
      w * x i - P.continuationAtArrival w c x (Function.update u i t) i := by
  unfold Instance.candidateGap Instance.continuationAtArrival
  rw [Function.update_self, unseen_replaceClock_erase]

/-- An actual offer hits a prescribed acceptance band with probability at most
its Lebesgue width bound. Candidate-clock replacement derives the conditional
uniform law while all other randomness is held fixed. -/
theorem Instance.acceptanceBand_probability {S : Type*} [MeasurableSpace S]
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure S) [IsProbabilityMeasure ν] {w c δ : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hδ : 0 ≤ δ) (i : Fin n) :
    (P.worldLaw ν).real {ω : World n S | |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ δ} ≤
      2 * δ / (c / (4 * (1 + (n : ℝ)))) := by
  let μ := P.worldLaw ν
  let E : Set (World n S) := {ω | |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ δ}
  let a := c / (4 * (1 + (n : ℝ)))
  let K := 2 * δ / a
  have ha : 0 < a := by dsimp [a]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hV : Measurable (fun ω : World n S ↦ P.continuationAtArrival w c ω.1 ω.2.1 i) :=
    P.measurable_continuationAtArrival hP hw hc.le
      (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
      (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hgap : Measurable (fun ω : World n S ↦ w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i) :=
    (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).sub hV
  have hE : MeasurableSet E := measurableSet_le (continuous_abs.measurable.comp hgap) measurable_const
  have hp := P.replaceClock_measurePreserving ν i
  have hpre := hE.preimage hp.measurable
  have hInner (ω : World n S) :
      Instance.uniformClock (Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E)) ≤ ENNReal.ofReal K := by
    let g := P.candidateGap w c i (ω.1 i) ω.2.1
    have hg := P.measurable_candidateGap hP hw.le hc.le i (ω.1 i) ω.2.1
    have hlevel : MeasurableSet {t : ℝ | |g t| ≤ δ} :=
      measurableSet_le (continuous_abs.measurable.comp hg) measurable_const
    have he : Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E) = {t : ℝ | |g t| ≤ δ} := by
      ext t
      change |w * ω.1 i - P.continuationAtArrival w c ω.1 (Function.update ω.2.1 i t) i| ≤ δ ↔
        |P.candidateGap w c i (ω.1 i) ω.2.1 t| ≤ δ
      rw [P.candidateGap_eq_replacedAcceptanceGap]
    rw [he, Instance.uniformClock, Measure.restrict_apply hlevel, inter_comm]
    exact ProphetSecretary.Analysis.volume_thresholdBand_le ha (P.candidateGap_slope hP hw hc.le i (ω.1 i) ω.2.1)
  have hbound : μ E ≤ ENNReal.ofReal K := by
    calc
      μ E = (μ.prod Instance.uniformClock) ((Instance.replaceClock i) ⁻¹' E) :=
        (hp.measure_preimage hE.nullMeasurableSet).symm
      _ = ∫⁻ ω, Instance.uniformClock (Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E)) ∂μ :=
        Measure.prod_apply hpre
      _ ≤ ∫⁻ _ω, ENNReal.ofReal K ∂μ := lintegral_mono hInner
      _ = ENNReal.ofReal K := by simp
  exact ENNReal.toReal_le_of_le_ofReal hK hbound

end ProphetSecretary.Model
