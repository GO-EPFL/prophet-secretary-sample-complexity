import ProphetSecretary.Limiting.FiniteIntensityPoisson
import ProphetSecretary.Probability.FiniteKernelIntegral
import Mathlib.MeasureTheory.Function.Floor

/-!
# Measurable chronological tags from the observed finite history

The rank at a clock is the natural count of strictly earlier observed points.
The tagged history is a measurable pushforward of the finite past measure.
No configuration label, total future count or unseen point is consulted.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

@[irreducible] noncomputable def finitePastRank (H : FiniteMeasure Point) (t : ℝ) : ℕ :=
  Nat.floor ((H : Measure Point).real {p | p.1<t})

lemma measurable_finitePastRank : Measurable (fun z : FiniteMeasure Point × ℝ => finitePastRank z.1 z.2) := by
  unfold finitePastRank
  have hF : Measurable (fun z : (FiniteMeasure Point × ℝ) × Point =>
      if z.2.1<z.1.2 then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_lt measurable_snd.fst measurable_fst.snd) measurable_const measurable_const
  have hL := ProphetSecretary.Probability.measurable_lintegral_finiteFamily
    (μ := fun z : FiniteMeasure Point × ℝ => z.1) measurable_fst hF
  have hEq : (fun z : FiniteMeasure Point × ℝ => ∫⁻ p, (if p.1<z.2 then (1 : ℝ≥0∞) else 0) ∂(z.1 : Measure Point))=
      (fun z => (z.1 : Measure Point) {p | p.1<z.2}) := by
    funext z
    have hZone : MeasurableSet {p : Point | p.1<z.2} := measurableSet_lt measurable_fst measurable_const
    simpa only [Set.indicator_apply,Set.mem_setOf_eq,one_mul] using
      (lintegral_indicator_const (μ := (z.1 : Measure Point)) hZone (1 : ℝ≥0∞))
  rw [hEq] at hL
  exact Nat.measurable_floor.comp hL.ennreal_toReal

noncomputable def tagPointByFiniteHistory {T : Type*} (σ : ℕ → T) (H : FiniteMeasure Point) (p : Point) : ℝ × (ℝ × T) :=
  (p.1,(p.2,σ (finitePastRank H p.1)))

lemma measurable_tagPointByFiniteHistory {T : Type*} [MeasurableSpace T] :
    Measurable (fun z : ((ℕ → T) × FiniteMeasure Point) × Point => tagPointByFiniteHistory z.1.1 z.1.2 z.2) := by
  have hEval : Measurable (fun z : (ℕ → T) × ℕ => z.1 z.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  have hRank : Measurable (fun z : ((ℕ → T) × FiniteMeasure Point) × Point => finitePastRank z.1.2 z.2.1) :=
    measurable_finitePastRank.comp (measurable_fst.snd.prodMk measurable_snd.fst)
  have hClock : Measurable (fun z : ((ℕ → T) × FiniteMeasure Point) × Point => z.2.1) := measurable_snd.fst
  have hValue : Measurable (fun z : ((ℕ → T) × FiniteMeasure Point) × Point => z.2.2) := measurable_snd.snd
  have hSeq : Measurable (fun z : ((ℕ → T) × FiniteMeasure Point) × Point => z.1.1) := measurable_fst.fst
  have hTag : Measurable (fun z : ((ℕ → T) × FiniteMeasure Point) × Point => z.1.1 (finitePastRank z.1.2 z.2.1)) :=
    hEval.comp (hSeq.prodMk hRank)
  exact hClock.prodMk (hValue.prodMk hTag)

noncomputable def chronologicalTaggedHistory {T : Type*} [MeasurableSpace T] (σ : ℕ → T) (H : FiniteMeasure Point) : Measure (ℝ × (ℝ × T)) :=
  (H : Measure Point).map (tagPointByFiniteHistory σ H)

lemma measurable_chronologicalTaggedHistory {T : Type*} [MeasurableSpace T] :
    Measurable (fun z : (ℕ → T) × FiniteMeasure Point => chronologicalTaggedHistory z.1 z.2) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have hPoint := measurable_tagPointByFiniteHistory (T := T)
  have hF : Measurable (fun z : ((ℕ → T) × FiniteMeasure Point) × Point =>
      if tagPointByFiniteHistory z.1.1 z.1.2 z.2∈S then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (hS.preimage hPoint) measurable_const measurable_const
  have hL := ProphetSecretary.Probability.measurable_lintegral_finiteFamily
    (μ := fun z : (ℕ → T) × FiniteMeasure Point => z.2) measurable_snd hF
  have hEq : (fun z : (ℕ → T) × FiniteMeasure Point => chronologicalTaggedHistory z.1 z.2 S)=
      fun z => ∫⁻ p, (if tagPointByFiniteHistory z.1 z.2 p∈S then (1 : ℝ≥0∞) else 0) ∂(z.2 : Measure Point) := by
    funext z
    have hG : Measurable (tagPointByFiniteHistory z.1 z.2) := hPoint.comp (measurable_const.prodMk measurable_id)
    rw [chronologicalTaggedHistory,Measure.map_apply hG hS]
    exact (by
      have h := lintegral_indicator_const (μ := (z.2 : Measure Point)) (hS.preimage hG) (1 : ℝ≥0∞)
      simpa only [Set.indicator_apply,Set.mem_preimage,one_mul] using h.symm)
  rw [hEq]
  exact hL

end ProphetSecretary.Limiting
