import ProphetSecretary.Limiting.HybridPositiveBand
import ProphetSecretary.Model.ClockReplacement

/-! # Retained-candidate hybrid band probability
Replacing one independent candidate clock exposes the moving-state band width.
The curve removes its own retained identity, including when its offer is zero.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def FiniteIntensityHybridInstance.retainedPositiveBand (B : FiniteIntensityHybridInstance n)
    {S : Type*} (w c b e : ℝ) (i : Fin n) : Set (Model.World n S) :=
  {ω | b ≤ ω.1 i ∧ |B.candidateGap w c (some i) (ω.1 i) ω.2.1 (ω.2.1 i)| ≤ e}

lemma FiniteIntensityHybridInstance.measurableSet_retainedPositiveBand (B : FiniteIntensityHybridInstance n)
    {S : Type*} [MeasurableSpace S] {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (b e : ℝ) (i : Fin n) :
    MeasurableSet (B.retainedPositiveBand (S := S) w c b e i) := by
  have hx : Measurable (fun ω : Model.World n S => ω.1 i) := (measurable_pi_apply i).comp measurable_fst
  have hu : Measurable (fun ω : Model.World n S => ω.2.1) := measurable_fst.comp measurable_snd
  have ht : Measurable (fun ω : Model.World n S => ω.2.1 i) := (measurable_pi_apply i).comp hu
  have hg := (B.measurable_candidateGap_joint hw hc (some i)).comp (hx.prodMk (hu.prodMk ht))
  exact (measurableSet_le measurable_const hx).inter
    (measurableSet_le (continuous_abs.measurable.comp hg) measurable_const)

theorem FiniteIntensityHybridInstance.retainedPositiveBand_probability {S : Type*} [MeasurableSpace S]
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (ν : Measure S) [IsProbabilityMeasure ν] {H w c b L e : ℝ}
    (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H)
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) (hL : B.tailCount (b / 4) ≤ L)
    (he0 : 0 ≤ e) (he : e ≤ w * b / 4) (i : Fin n) :
    (B.individuals.worldLaw ν).real (B.retainedPositiveBand (S := S) w c b e i) ≤
      (2 * e / (c * Model.positiveBandDuration H w c b L)) * (B.individuals.law i).real (Ici b) := by
  let μ := B.individuals.worldLaw ν
  let E := B.retainedPositiveBand (S := S) w c b e i
  let F : Set (Model.World n S) := {ω | b ≤ ω.1 i}
  let K := 2 * e / (c * Model.positiveBandDuration H w c b L)
  have hL0 : 0 ≤ L := (B.tailCount_nonnegative _).trans hL
  have hk : 0 < Model.positiveBandDuration H w c b L := Model.positiveBandDuration_pos hH hw hc hb hL0
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE := B.measurableSet_retainedPositiveBand hw.le hc.le b e i (S := S)
  have hXi : Measurable (fun ω : Model.World n S => ω.1 i) := (measurable_pi_apply i).comp measurable_fst
  have hF : MeasurableSet F := measurableSet_le measurable_const hXi
  have hp := B.individuals.replaceClock_measurePreserving ν i
  have hpre := hE.preimage hp.measurable
  have hInner (ω : Model.World n S) :
      Model.Instance.uniformClock (Prod.mk ω ⁻¹' ((Model.Instance.replaceClock i) ⁻¹' E)) ≤
        F.indicator (fun _ => ENNReal.ofReal K) ω := by
    by_cases hx : b ≤ ω.1 i
    · rw [Set.indicator_of_mem (show ω ∈ F from hx)]
      let g := B.candidateGap w c (some i) (ω.1 i) ω.2.1
      have hg := B.measurable_candidateGap hw.le hc.le (some i) (ω.1 i) ω.2.1
      have hm : MeasurableSet {t : ℝ | |g t| ≤ e} :=
        measurableSet_le (continuous_abs.measurable.comp hg) measurable_const
      have heq : Prod.mk ω ⁻¹' ((Model.Instance.replaceClock i) ⁻¹' E) = {t : ℝ | |g t| ≤ e} := by
        ext t
        simp only [Set.mem_preimage,Set.mem_setOf_eq,E,FiniteIntensityHybridInstance.retainedPositiveBand,
          Model.Instance.replaceClock,Function.update_self,g,B.candidateGap_update_clock,hx,true_and]
      rw [heq, Model.Instance.uniformClock, Measure.restrict_apply hm, inter_comm]
      exact B.candidateGap_positiveBand_volume ha hH hCap hw hc hb hL he (some i) hx ω.2.1
    · rw [Set.indicator_of_notMem (show ω ∉ F from hx)]
      have heq : Prod.mk ω ⁻¹' ((Model.Instance.replaceClock i) ⁻¹' E) = ∅ := by
        ext t
        simp only [Set.mem_preimage,Set.mem_setOf_eq,E,FiniteIntensityHybridInstance.retainedPositiveBand,
          Model.Instance.replaceClock,hx,false_and,Set.mem_empty_iff_false]
      rw [heq, measure_empty]
  have hval : MeasurePreserving (fun ω : Model.World n S => ω.1 i) μ (B.individuals.law i) :=
    (measurePreserving_eval B.individuals.law i).comp
      (measurePreserving_fst (μ := B.individuals.valuesLaw) (ν := (Model.Instance.clocksLaw n).prod ν))
  have hMarg : μ F = (B.individuals.law i) (Ici b) := hval.measure_preimage measurableSet_Ici.nullMeasurableSet
  have hboundE : μ E ≤ ENNReal.ofReal K * (B.individuals.law i) (Ici b) := by
    calc
      μ E = (μ.prod Model.Instance.uniformClock) ((Model.Instance.replaceClock i) ⁻¹' E) :=
        (hp.measure_preimage hE.nullMeasurableSet).symm
      _ = ∫⁻ ω, Model.Instance.uniformClock (Prod.mk ω ⁻¹' ((Model.Instance.replaceClock i) ⁻¹' E)) ∂μ := Measure.prod_apply hpre
      _ ≤ ∫⁻ ω, F.indicator (fun _ => ENNReal.ofReal K) ω ∂μ := lintegral_mono hInner
      _ = ENNReal.ofReal K * μ F := lintegral_indicator_const hF _
      _ = ENNReal.ofReal K * (B.individuals.law i) (Ici b) := by rw [hMarg]
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hboundE
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using hreal

/-- Union over the actual retained identities, with no enumeration of their
possible unseen states. -/
theorem FiniteIntensityHybridInstance.any_retainedPositiveBand_probability
    {S : Type*} [MeasurableSpace S] (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    (ν : Measure S) [IsProbabilityMeasure ν] {H w c b L e : ℝ}
    (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H) (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    (hL : B.tailCount (b/4) ≤ L) (he0 : 0 ≤ e) (he : e ≤ w*b/4) :
    (B.individuals.worldLaw ν).real {z : Model.World n S | ∃ i : Fin n,
      z ∈ B.retainedPositiveBand w c b e i} ≤
      (2*e/(c*Model.positiveBandDuration H w c b L))*B.individuals.tailCount (b/2) := by
  rw [Set.setOf_exists]
  calc
    _ ≤ ∑ i : Fin n, (B.individuals.worldLaw ν).real (B.retainedPositiveBand w c b e i) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin n, (2*e/(c*Model.positiveBandDuration H w c b L))*(B.individuals.law i).real (Ici b) :=
      Finset.sum_le_sum fun i _ => B.retainedPositiveBand_probability ha ν hH hCap hw hc hb hL he0 he i
    _ = (2*e/(c*Model.positiveBandDuration H w c b L))*(∑ i : Fin n, (B.individuals.law i).real (Ici b)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (B.individuals.sum_probability_ge_le_tailCount_half hb) (by
      have := Model.positiveBandDuration_pos hH hw hc hb ((B.tailCount_nonnegative _).trans hL)
      positivity)

end ProphetSecretary.Limiting
