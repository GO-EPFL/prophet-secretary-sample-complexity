import ProphetSecretary.Statistics.DataSelectedClockLossIntegrability
import ProphetSecretary.Statistics.EmpiricalClockLossEntrances
import ProphetSecretary.Model.ClockPostLevelLoss
import ProphetSecretary.Model.ClockPostFarLoss
import ProphetSecretary.Model.ClockPostEarlySixthLoss

/-!
# Measurable candidate-time regions at a selected scalar

The critical entrance uses the true law. The scalar Z depends only on
training coordinates; each time integral keeps that scalar fixed.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ}

noncomputable def clockLossRegion (P : Instance n) (Z : ((Fin n × Fin k) → ℝ) → ℝ)
    (hi a b : ℝ) (above : Bool)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : Set ℝ :=
  Ioc (P.trueCriticalEntrance hi a q.2) 1 ∩
    {t | if above then b ≤ P.clockContinuation (Z q.1) q.2 t
      else P.clockContinuation (Z q.1) q.2 t < b}

noncomputable def clockRegionLoss (P : Instance n) (Z : ((Fin n × Fin k) → ℝ) → ℝ)
    (hi a b : ℝ) (above : Bool)
    (L : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) → ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : ℝ :=
  ∫ t in clockLossRegion P Z hi a b above q, L (q,t)

lemma measurableSet_clockLossRegion_pair (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} (hZ : Measurable Z) (hZ0 : ∀ a, 0 ≤ Z a)
    (hi a b : ℝ) (above : Bool) :
    MeasurableSet {qt : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) |
      qt.2 ∈ clockLossRegion P Z hi a b above qt.1} := by
  have hσ : Measurable (fun qt : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) =>
      P.trueCriticalEntrance hi a qt.1.2) :=
    (P.measurable_trueCriticalEntrance hi a).comp (measurable_snd.comp measurable_fst)
  have hv := P.measurable_clockContinuation_parameters hP
    (hZ.comp (measurable_fst.comp measurable_fst)) measurable_snd
    (fun i => (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
    (fun qt => hZ0 qt.1.1)
  cases above
  · exact ((measurableSet_lt hσ measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)).inter (measurableSet_lt hv measurable_const)
  · exact ((measurableSet_lt hσ measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)).inter (measurableSet_le measurable_const hv)

lemma measurableSet_clockLossRegion (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} (hZ0 : ∀ a, 0 ≤ Z a)
    (hi a b : ℝ) (above : Bool) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    MeasurableSet (clockLossRegion P Z hi a b above q) := by
  have hv := P.measurable_clockContinuation hP (hZ0 q.1) q.2
  cases above
  · exact measurableSet_Ioc.inter (measurableSet_lt hv measurable_const)
  · exact measurableSet_Ioc.inter (measurableSet_le measurable_const hv)

lemma measurable_clockRegionLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} (hZ : Measurable Z) (hZ0 : ∀ a, 0 ≤ Z a)
    (hi a b : ℝ) (above : Bool)
    {L : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) → ℝ} (hL : Measurable L) :
    Measurable (clockRegionLoss P Z hi a b above L) := by
  let D := {qt : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) |
    qt.2 ∈ clockLossRegion P Z hi a b above qt.1}
  have hD : MeasurableSet D := measurableSet_clockLossRegion_pair P hP hZ hZ0 hi a b above
  have hm := (hL.indicator hD).stronglyMeasurable.integral_prod_right' (ν := volume)
  have heq : clockRegionLoss P Z hi a b above L = (fun q => ∫ t, D.indicator L (q,t)) := by
    funext q
    symm
    change (∫ t, (clockLossRegion P Z hi a b above q).indicator (fun s => L (q,s)) t) = _
    exact integral_indicator (measurableSet_clockLossRegion P hP hZ0 hi a b above q)
  rw [heq]
  exact hm.measurable

lemma clockRegionLoss_nonnegative (P : Instance n) (Z : ((Fin n × Fin k) → ℝ) → ℝ)
    (hi a b : ℝ) (above : Bool)
    {L : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) → ℝ}
    (hL : ∀ q t, 0 ≤ L (q,t)) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    0 ≤ clockRegionLoss P Z hi a b above L q := integral_nonneg fun t => hL q t

noncomputable def dataSelectedClockLossDirection (P : Instance n) [NeZero k]
    (Z : ((Fin n × Fin k) → ℝ) → ℝ) (reverse : Bool) (x : ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : ℝ :=
  if reverse then dataSelectedClockLossReverse P Z x q t else dataSelectedClockLoss P Z x q t

lemma measurable_dataSelectedClockLossDirection_pair (P : Instance n) [NeZero k]
    (hP : Integrable Instance.maximum P.valuesLaw)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} (hZ : Measurable Z) (hZ0 : ∀ a, 0 ≤ Z a)
    (reverse : Bool) (x : ℝ) :
    Measurable (fun qt : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) =>
      dataSelectedClockLossDirection P Z reverse x qt.1 qt.2) := by
  cases reverse
  · exact (measurable_dataSelectedClockLoss_pair P hP hZ hZ0 x).1
  · exact (measurable_dataSelectedClockLoss_pair P hP hZ hZ0 x).2

lemma dataSelectedClockLossDirection_nonnegative (P : Instance n) [NeZero k]
    (Z : ((Fin n × Fin k) → ℝ) → ℝ) (reverse : Bool) (x : ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) :
    0 ≤ dataSelectedClockLossDirection P Z reverse x q t := by
  cases reverse
  · exact dataSelectedClockLoss_nonnegative _ _ _ _ _
  · exact dataSelectedClockLossReverse_nonnegative _ _ _ _ _

lemma measurable_dataSelectedClockLossDirection_time (P : Instance n) [NeZero k]
    (hP : Integrable Instance.maximum P.valuesLaw)
    (Z : ((Fin n × Fin k) → ℝ) → ℝ) (hZ0 : ∀ a, 0 ≤ Z a)
    (reverse : Bool) (x : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    Measurable (fun t => dataSelectedClockLossDirection P Z reverse x q t) := by
  cases reverse
  · exact measurable_empiricalClockGapLoss P hP (fun _ _ => measurable_const)
      measurable_const measurable_id measurable_const (fun _ => measurable_const) (fun _ => hZ0 q.1)
  · exact measurable_trueClockGapLossEmpiricalEval P hP (fun _ _ => measurable_const)
      measurable_const measurable_id measurable_const (fun _ => measurable_const) (fun _ => hZ0 q.1)

/-- Restricting a common post-entrance band bound to a measurable time region. -/
lemma clock_lossGapBound_restrict (P : Instance n) {z x E σ : ℝ} (u : Fin n → ℝ)
    {S : Set ℝ} (hS : MeasurableSet S) (hsub : S ⊆ Ioc σ 1)
    {loss : ℝ → ℝ}
    (hafter : ∀ t ∈ Ioc σ 1, loss t ≤ if |x-P.clockContinuation z u t| ≤ E then E else 0) :
    ∀ᵐ t ∂volume.restrict S, loss t ≤
      (S ∩ {t | |x-P.clockContinuation z u t| ≤ E}).indicator (fun _ => E) t := by
  filter_upwards [ae_restrict_mem hS] with t ht
  have h := hafter t (hsub ht)
  by_cases hb : |x-P.clockContinuation z u t| ≤ E
  · simpa only [if_pos hb,indicator_of_mem (show t ∈ S ∩ {t | |x-P.clockContinuation z u t| ≤ E} from ⟨ht,hb⟩)] using h
  · simpa only [if_neg hb,indicator_of_notMem (show t ∉ S ∩ {t | |x-P.clockContinuation z u t| ≤ E} from fun h => hb h.2)] using h

end ProphetSecretary.Model
