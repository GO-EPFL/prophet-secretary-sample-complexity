import ProphetSecretary.Model.ScalarBands
import ProphetSecretary.Model.TruncatedReward
import Mathlib.Tactic.FieldSimp

/-!
# Positive-level acceptance bands

On a boundary band for a candidate worth at least `b`, the later state's value remains
at least `3wb/4`. An actual base-optimal policy then has duration bounded below through
positive-level tail counts. Its fixed-policy horizon support, together with monotonicity
under adding unseen identities, gives a band-width estimate independent of instance size.
No derivative at remaining horizon zero is needed.
-/

open MeasureTheory Set Filter
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Model

/-- Explicit normalized-duration lower bound in a positive continuation band. -/
noncomputable def positiveBandDuration (H w c b L : ℝ) : ℝ :=
  w * b / (2 * (2 * w * H * L + c))

lemma positiveBandDuration_pos {H w c b L : ℝ} (hH : 0 ≤ H) (hw : 0 < w)
    (hc : 0 < c) (hb : 0 < b) (hL : 0 ≤ L) : 0 < positiveBandDuration H w c b L := by
  unfold positiveBandDuration
  positivity

variable {n : ℕ}

/-- The slope condition is required only between points in the actual acceptance band.
The later state's base optimizer supplies the support, including at remaining time zero. -/
lemma Instance.candidateGap_positiveBand_slope (P : Instance n) {H w c b L e : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H)
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) (hL : P.tailCount (b / 4) ≤ L)
    (he : e ≤ w * b / 4) (i : Fin n) {x : ℝ} (hx : b ≤ x) (u : Fin n → ℝ) :
    ProphetSecretary.Analysis.SlopeLowerBoundOn (P.candidateGap w c i x u)
      (c * positiveBandDuration H w c b L)
      (ProphetSecretary.Analysis.thresholdBand (P.candidateGap w c i x u) e) := by
  let hP := P.integrable_maximum_of_bounded hbound
  intro t ht s hs hts
  let A := otherUnseen u i t
  let B := otherUnseen u i s
  let Q := P.restrictTo B
  let hQ := P.restrictTo_integrable_maximum B hP
  have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.1.2
  have hs0 : 0 ≤ 1 - s := sub_nonneg.mpr hs.1.2
  have hs1 : 1 - s ≤ 1 := sub_le_self 1 hs.1.1
  have hgap : P.candidateGap w c i x u s ≤ e :=
    (le_abs_self _).trans (show |P.candidateGap w c i x u s| ≤ e from hs.2)
  unfold Instance.candidateGap at hgap
  rw [max_eq_right hs0] at hgap
  have hlevel : 3 * w * b / 4 ≤ remainingScalarValue Q w c (1 - s) := by
    change 3 * w * b / 4 ≤ P.continuationValue B (1 - s) w c
    change w * x - P.continuationValue B (1 - s) w c ≤ e at hgap
    have hwb := mul_le_mul_of_nonneg_left hx hw.le
    nlinarith
  have hQbound : ∀ j, ∀ᵐ y ∂Q.law j, y ≤ H := fun j => hbound (stateEmbedding B j)
  have hQL : Q.tailCount (b / 4) ≤ L := (P.tailCount_restrictTo_le B (b / 4)).trans hL
  have hT0 := Q.valuePolicy_duration_ge_positiveValue hH hb hQbound hw hc hs0 hs1 hQL hlevel
  have hT : positiveBandDuration H w c b L ≤
      (Q.valuePolicy hQ hw.le (mul_nonneg hc.le hs0)).expectedDuration Q := hT0
  have hsupp := Q.remainingHorizon_support (u := 1 - t) (v := 1 - s) hQ hw hc.le ht0 hs0
  have hm := P.optimalScalarValue_restrictTo_mono hP (otherUnseen_antitone u i hts) hw.le (mul_nonneg hc.le ht0)
  change P.continuationValue B (1 - t) w c ≤ P.continuationValue A (1 - t) w c at hm
  have hmul := mul_le_mul_of_nonneg_left hT (mul_nonneg hc.le
    (sub_nonneg.mpr (sub_le_sub_left hts 1)))
  unfold Instance.candidateGap
  rw [max_eq_right ht0, max_eq_right hs0]
  change (c * positiveBandDuration H w c b L) * (s - t) ≤
    (w * x - P.continuationValue B (1 - s) w c) - (w * x - P.continuationValue A (1 - t) w c)
  change P.continuationValue B (1 - s) w c + c * ((1 - t) - (1 - s)) *
    (Q.valuePolicy hQ hw.le (mul_nonneg hc.le hs0)).expectedDuration Q ≤
      P.continuationValue B (1 - t) w c at hsupp
  nlinarith

private lemma volume_band_le_of_bandSlope {g : ℝ → ℝ} {a e : ℝ} (ha : 0 < a)
    (hslope : ProphetSecretary.Analysis.SlopeLowerBoundOn g a (ProphetSecretary.Analysis.thresholdBand g e)) :
    volume (ProphetSecretary.Analysis.thresholdBand g e) ≤ ENNReal.ofReal (2 * e / a) := by
  apply (Real.volume_le_diam _).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro t ht s hs
  have hgt := abs_le.mp (show |g t| ≤ e from ht.2)
  have hgs := abs_le.mp (show |g s| ≤ e from hs.2)
  rcases le_total t s with hts | hst
  · have h := hslope t ht s hs hts
    have hd : s - t ≤ 2 * e / a := (le_div_iff₀ ha).mpr (by nlinarith)
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using hd
  · have h := hslope s hs t ht hst
    have hd : t - s ≤ 2 * e / a := (le_div_iff₀ ha).mpr (by nlinarith)
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst)] using hd

/-- The positive-level band has a width depending on tail counts, not the number of
zero, small, or total offers. This estimate is pathwise in all the other clocks. -/
theorem Instance.candidateGap_positiveBand_volume (P : Instance n) {H w c b L e : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H)
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) (hL : P.tailCount (b / 4) ≤ L)
    (he : e ≤ w * b / 4) (i : Fin n) {x : ℝ} (hx : b ≤ x) (u : Fin n → ℝ) :
    volume (ProphetSecretary.Analysis.thresholdBand (P.candidateGap w c i x u) e) ≤
      ENNReal.ofReal (2 * e / (c * positiveBandDuration H w c b L)) := by
  have hL0 : 0 ≤ L := (P.tailCount_nonnegative _).trans hL
  exact volume_band_le_of_bandSlope (mul_pos hc (positiveBandDuration_pos hH hw hc hb hL0))
    (P.candidateGap_positiveBand_slope hH hbound hw hc hb hL he i hx u)

/-- An actual positive offer whose weighted acceptance gap lies near zero. This event
has no reach conditioning and may be used for any competing online policy. -/
def Instance.positiveAcceptanceBand {S : Type*} (P : Instance n) (w c b e : ℝ) (i : Fin n) : Set (World n S) :=
  {ω | b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e}

lemma Instance.measurableSet_positiveAcceptanceBand {S : Type*} [MeasurableSpace S]
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (b e : ℝ) (i : Fin n) :
    MeasurableSet (P.positiveAcceptanceBand (S := S) w c b e i) := by
  have hx : Measurable (fun ω : World n S => ω.1 i) := (measurable_pi_apply i).comp measurable_fst
  have hv : Measurable (fun ω : World n S => P.continuationAtArrival w c ω.1 ω.2.1 i) :=
    P.measurable_continuationAtArrival hP hw hc
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  exact (measurableSet_le measurable_const hx).inter
    (measurableSet_le (continuous_abs.measurable.comp ((measurable_const.mul hx).sub hv)) measurable_const)

/-- A candidate's independent uniform clock contributes its band width, multiplied by
its probability of exceeding the positive level. This is derived by clock replacement. -/
theorem Instance.positiveAcceptanceBand_probability {S : Type*} [MeasurableSpace S]
    (P : Instance n) (ν : Measure S) [IsProbabilityMeasure ν] {H w c b L e : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H)
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) (hL : P.tailCount (b / 4) ≤ L)
    (he0 : 0 ≤ e) (he : e ≤ w * b / 4) (i : Fin n) :
    (P.worldLaw ν).real (P.positiveAcceptanceBand (S := S) w c b e i) ≤
      (2 * e / (c * positiveBandDuration H w c b L)) * (P.law i).real (Ici b) := by
  let hP := P.integrable_maximum_of_bounded hbound
  let μ := P.worldLaw ν
  let E := P.positiveAcceptanceBand (S := S) w c b e i
  let F : Set (World n S) := {ω | b ≤ ω.1 i}
  let K := 2 * e / (c * positiveBandDuration H w c b L)
  have hL0 : 0 ≤ L := (P.tailCount_nonnegative _).trans hL
  have hk : 0 < positiveBandDuration H w c b L := positiveBandDuration_pos hH hw hc hb hL0
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE := P.measurableSet_positiveAcceptanceBand hP hw hc.le b e i (S := S)
  have hXi : Measurable (fun ω : World n S => ω.1 i) := (measurable_pi_apply i).comp measurable_fst
  have hF : MeasurableSet F := measurableSet_le measurable_const hXi
  have hp := P.replaceClock_measurePreserving ν i
  have hpre := hE.preimage hp.measurable
  have hInner (ω : World n S) :
      Instance.uniformClock (Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E)) ≤
        F.indicator (fun _ => ENNReal.ofReal K) ω := by
    by_cases hx : b ≤ ω.1 i
    · rw [Set.indicator_of_mem (show ω ∈ F from hx)]
      let g := P.candidateGap w c i (ω.1 i) ω.2.1
      have hg := P.measurable_candidateGap hP hw.le hc.le i (ω.1 i) ω.2.1
      have hm : MeasurableSet {t : ℝ | |g t| ≤ e} :=
        measurableSet_le (continuous_abs.measurable.comp hg) measurable_const
      have heq : Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E) = {t : ℝ | |g t| ≤ e} := by
        ext t
        change (b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 (Function.update ω.2.1 i t) i| ≤ e) ↔
          |P.candidateGap w c i (ω.1 i) ω.2.1 t| ≤ e
        rw [P.candidateGap_eq_replacedAcceptanceGap]
        simp only [hx, true_and]
      rw [heq, Instance.uniformClock, Measure.restrict_apply hm, inter_comm]
      exact P.candidateGap_positiveBand_volume hH hbound hw hc hb hL he i hx ω.2.1
    · rw [Set.indicator_of_notMem (show ω ∉ F from hx)]
      have heq : Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E) = ∅ := by
        ext t
        change (b ≤ ω.1 i ∧ _) ↔ False
        simp only [hx, false_and]
      rw [heq, measure_empty]
  have hval : MeasurePreserving (fun ω : World n S => ω.1 i) μ (P.law i) :=
    (measurePreserving_eval P.law i).comp
      (measurePreserving_fst (μ := P.valuesLaw) (ν := (Instance.clocksLaw n).prod ν))
  have hMarg : μ F = (P.law i) (Ici b) := hval.measure_preimage measurableSet_Ici.nullMeasurableSet
  have hboundE : μ E ≤ ENNReal.ofReal K * (P.law i) (Ici b) := by
    calc
      μ E = (μ.prod Instance.uniformClock) ((Instance.replaceClock i) ⁻¹' E) :=
        (hp.measure_preimage hE.nullMeasurableSet).symm
      _ = ∫⁻ ω, Instance.uniformClock (Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E)) ∂μ := Measure.prod_apply hpre
      _ ≤ ∫⁻ ω, F.indicator (fun _ => ENNReal.ofReal K) ω ∂μ := lintegral_mono hInner
      _ = ENNReal.ofReal K * μ F := lintegral_indicator_const hF _
      _ = ENNReal.ofReal K * (P.law i) (Ici b) := by rw [hMarg]
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hboundE
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using hreal

lemma Instance.sum_probability_ge_le_tailCount_half (P : Instance n) {b : ℝ} (hb : 0 < b) :
    (∑ i : Fin n, (P.law i).real (Ici b)) ≤ P.tailCount (b / 2) := by
  apply Finset.sum_le_sum
  intro i _
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro x hx
  change b / 2 < x
  have hx' : b ≤ x := hx
  linarith

/-- Uniform positive-level near-boundary probability for small error bands. The two
explicit tail bounds are the only dependence on the number or laws of the offers. -/
theorem Instance.any_positiveAcceptanceBand_probability_small {S : Type*} [MeasurableSpace S]
    (P : Instance n) (ν : Measure S) [IsProbabilityMeasure ν] {H w c b L4 L2 e : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H)
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    (hL4 : P.tailCount (b / 4) ≤ L4) (hL2 : P.tailCount (b / 2) ≤ L2)
    (he0 : 0 ≤ e) (he : e ≤ w * b / 4) :
    (P.worldLaw ν).real {ω : World n S | ∃ i : Fin n,
      b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e} ≤
      (2 * L2 / (c * positiveBandDuration H w c b L4)) * e := by
  let K := 2 * e / (c * positiveBandDuration H w c b L4)
  have hL40 : 0 ≤ L4 := (P.tailCount_nonnegative _).trans hL4
  have hK : 0 ≤ K := by dsimp [K]; have := positiveBandDuration_pos hH hw hc hb hL40; positivity
  have hSet : {ω : World n S | ∃ i : Fin n,
      b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e} =
      ⋃ i : Fin n, P.positiveAcceptanceBand w c b e i := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, Instance.positiveAcceptanceBand]
  rw [hSet]
  calc
    (P.worldLaw ν).real (⋃ i : Fin n, P.positiveAcceptanceBand w c b e i) ≤
        ∑ i : Fin n, (P.worldLaw ν).real (P.positiveAcceptanceBand w c b e i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin n, K * (P.law i).real (Ici b) := Finset.sum_le_sum
      (fun i _ => P.positiveAcceptanceBand_probability ν hH hbound hw hc hb hL4 he0 he i)
    _ = K * (∑ i : Fin n, (P.law i).real (Ici b)) := (Finset.mul_sum _ _ _).symm
    _ ≤ K * P.tailCount (b / 2) := mul_le_mul_of_nonneg_left (P.sum_probability_ge_le_tailCount_half hb) hK
    _ ≤ K * L2 := mul_le_mul_of_nonneg_left hL2 hK
    _ = (2 * L2 / (c * positiveBandDuration H w c b L4)) * e := by dsimp [K]; ring

/-- One explicit constant works for all nonnegative band widths. -/
noncomputable def stabilityBandConstant (H w c b L4 L2 : ℝ) : ℝ :=
  2 * L2 / (c * positiveBandDuration H w c b L4) + 4 / (w * b)

theorem Instance.any_positiveAcceptanceBand_probability {S : Type*} [MeasurableSpace S]
    (P : Instance n) (ν : Measure S) [IsProbabilityMeasure ν] {H w c b L4 L2 e : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H)
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    (hL4 : P.tailCount (b / 4) ≤ L4) (hL2 : P.tailCount (b / 2) ≤ L2) (he0 : 0 ≤ e) :
    (P.worldLaw ν).real {ω : World n S | ∃ i : Fin n,
      b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e} ≤
        stabilityBandConstant H w c b L4 L2 * e := by
  have hL40 : 0 ≤ L4 := (P.tailCount_nonnegative _).trans hL4
  have hL20 : 0 ≤ L2 := (P.tailCount_nonnegative _).trans hL2
  have hk := positiveBandDuration_pos hH hw hc hb hL40
  have hsmall0 : 0 ≤ 2 * L2 / (c * positiveBandDuration H w c b L4) := by positivity
  have hbase0 : 0 ≤ 4 / (w * b) := by positivity
  by_cases he : e ≤ w * b / 4
  · exact (P.any_positiveAcceptanceBand_probability_small ν hH hbound hw hc hb hL4 hL2 he0 he).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hbase0) he0)
  · have he' : w * b / 4 ≤ e := le_of_not_ge he
    have hwb : 0 < w * b := mul_pos hw hb
    have hone : 1 ≤ (4 / (w * b)) * e := by
      have h : 1 ≤ (4 * e) / (w * b) := (le_div_iff₀ hwb).mpr (by nlinarith)
      simpa only [div_mul_eq_mul_div] using h
    exact (measureReal_le_one.trans hone).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hsmall0) he0)

/-- A single explicit constant for normalized weights bounded away from zero. -/
noncomputable def uniformStabilityBandConstant (H δ b L4 L2 : ℝ) : ℝ :=
  4 * L2 * (2 * H * L4 + 1) / (δ ^ 2 * b) + 4 / (δ * b)

lemma stabilityBandConstant_le_uniform {H δ w c b L4 L2 : ℝ}
    (hH : 0 ≤ H) (hδ : 0 < δ) (hb : 0 < b) (hL4 : 0 ≤ L4) (hL2 : 0 ≤ L2)
    (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hw1 : w ≤ 1) (hc1 : c ≤ 1) :
    stabilityBandConstant H w c b L4 L2 ≤ uniformStabilityBandConstant H δ b L4 L2 := by
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  have hD : 2 * w * H * L4 + c ≤ 2 * H * L4 + 1 := by
    have h := mul_le_mul_of_nonneg_right hw1 (mul_nonneg hH hL4)
    nlinarith
  have hD0 : 0 < 2 * (2 * w * H * L4 + c) := by positivity
  have hM0 : 0 < 2 * H * L4 + 1 := by positivity
  let k0 := δ * b / (2 * (2 * H * L4 + 1))
  have hk0 : 0 < k0 := by dsimp [k0]; positivity
  have hinv := one_div_le_one_div_of_le hD0 (mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 2))
  have hk : k0 ≤ positiveBandDuration H w c b L4 := by
    calc
      k0 = (δ * b) * (1 / (2 * (2 * H * L4 + 1))) := by dsimp [k0]; ring
      _ ≤ (δ * b) * (1 / (2 * (2 * w * H * L4 + c))) :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg hδ.le hb.le)
      _ = δ * b / (2 * (2 * w * H * L4 + c)) := by ring
      _ ≤ w * b / (2 * (2 * w * H * L4 + c)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hwδ hb.le) hD0.le
      _ = positiveBandDuration H w c b L4 := rfl
  have ha := mul_le_mul hcδ hk hk0.le hc.le
  have hia := one_div_le_one_div_of_le (mul_pos hδ hk0) ha
  have hsmall : 2 * L2 / (c * positiveBandDuration H w c b L4) ≤
      4 * L2 * (2 * H * L4 + 1) / (δ ^ 2 * b) := by
    calc
      _ = (2 * L2) * (1 / (c * positiveBandDuration H w c b L4)) := by ring
      _ ≤ (2 * L2) * (1 / (δ * k0)) := mul_le_mul_of_nonneg_left hia (by positivity)
      _ = 4 * L2 * (2 * H * L4 + 1) / (δ ^ 2 * b) := by
        dsimp [k0]
        field_simp
        ring
  have hib := one_div_le_one_div_of_le (mul_pos hδ hb) (mul_le_mul_of_nonneg_right hwδ hb.le)
  have hbase : 4 / (w * b) ≤ 4 / (δ * b) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using mul_le_mul_of_nonneg_left hib (by norm_num : (0 : ℝ) ≤ 4)
  exact add_le_add hsmall hbase

lemma uniformStabilityBandConstant_positive {H δ b L4 L2 : ℝ}
    (hH : 0 ≤ H) (hδ : 0 < δ) (hb : 0 < b) (hL4 : 0 ≤ L4) (hL2 : 0 ≤ L2) :
    0 < uniformStabilityBandConstant H δ b L4 L2 := by
  unfold uniformStabilityBandConstant
  positivity

/-- Uniformity over every finite instance size and all normalized weights in a fixed
interior interval. The constant depends only on the displayed cap, level and tail bounds. -/
theorem Instance.any_positiveAcceptanceBand_probability_uniform {S : Type*} [MeasurableSpace S]
    (P : Instance n) (ν : Measure S) [IsProbabilityMeasure ν] {H δ w c b L4 L2 e : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H)
    (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1) (hb : 0 < b)
    (hL4 : P.tailCount (b / 4) ≤ L4) (hL2 : P.tailCount (b / 2) ≤ L2) (he0 : 0 ≤ e) :
    (P.worldLaw ν).real {ω : World n S | ∃ i : Fin n,
      b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e} ≤
        uniformStabilityBandConstant H δ b L4 L2 * e := by
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  have hw1 : w ≤ 1 := by linarith
  have hc1 : c ≤ 1 := by linarith
  have hL40 : 0 ≤ L4 := (P.tailCount_nonnegative _).trans hL4
  have hL20 : 0 ≤ L2 := (P.tailCount_nonnegative _).trans hL2
  exact (P.any_positiveAcceptanceBand_probability ν hH hbound hw hc hb hL4 hL2 he0).trans
    (mul_le_mul_of_nonneg_right (stabilityBandConstant_le_uniform hH hδ hb hL40 hL20 hwδ hcδ hw1 hc1) he0)

end ProphetSecretary.Model


