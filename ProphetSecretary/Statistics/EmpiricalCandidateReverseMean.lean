import ProphetSecretary.Statistics.EmpiricalCandidateOtherClockMean

/-!
# Reverse local loss under the empirical candidate law

The true canonical rule is evaluated under the empirical law. Its candidate
integral is exactly the average of losses at the candidate's own stored sample
values; its continuation uses only the other sample rows. This algebra holds
at every real array before the fixed-weight averaging argument.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def empiricalReverseOtherCandidateLossMean (P : Instance n) (a : (Fin n × Fin k) → ℝ)
    (z : ℝ) (i : Fin n) (v : Fin (Finset.univ.erase i).card → ℝ) : ℝ :=
  (k:ℝ)⁻¹ * ∑ l : Fin k, ∫ t, trueClockGapLossEmpiricalEval (P.restrictTo (Finset.univ.erase i))
    (reservoirCoordinates.symm (restrictTrainingCoordinates (Finset.univ.erase i) a)) z v (max 0 (a (i,l))) t ∂Instance.uniformClock

lemma candidateLossMean_true_empirical_eq_sampleAverage (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) (i : Fin n) (u : Fin n → ℝ) :
    candidateLossMean P (totalEmpiricalInstance (reservoirCoordinates.symm a)) hP z hz i u =
      empiricalReverseOtherCandidateLossMean P a z i (u ∘ stateEmbedding (Finset.univ.erase i)) := by
  unfold candidateLossMean
  rw [totalEmpiricalInstance_integral]
  apply congrArg ((k:ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro l _
  apply integral_congr_ae
  exact Eventually.of_forall fun t => trueCanonicalCandidateLoss_empiricalEval_eq_otherGaps P hP a hz i u (max 0 (a (i,l))) t

lemma measurable_empiricalReverseOtherCandidateLossMean (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) (i : Fin n) : Measurable (empiricalReverseOtherCandidateLossMean P a z i) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro l _
  let A := (Finset.univ : Finset (Fin n)).erase i
  let y := reservoirCoordinates.symm (restrictTrainingCoordinates A a)
  have hm : Measurable (fun q : (Fin A.card → ℝ) × ℝ =>
      trueClockGapLossEmpiricalEval (P.restrictTo A) y z q.1 (max 0 (a (i,l))) q.2) :=
    measurable_trueClockGapLossEmpiricalEval (P.restrictTo A) (P.restrictTo_integrable_maximum A hP)
      (fun _ _ => measurable_const) measurable_const measurable_snd measurable_const
      (fun j => (measurable_pi_apply j).comp measurable_fst) (fun _ => hz)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν:=Instance.uniformClock)).measurable

/-- Projecting clocks is exact also for the empirical-evaluation direction. -/
theorem empirical_reverse_candidateMean_integral_otherClocks (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) (i : Fin n) :
    Integrable (empiricalReverseOtherCandidateLossMean P a z i) (Instance.clocksLaw (Finset.univ.erase i).card) ∧
    (∫ u, candidateLossMean P (totalEmpiricalInstance (reservoirCoordinates.symm a)) hP z hz i u ∂Instance.clocksLaw n) =
      ∫ v, empiricalReverseOtherCandidateLossMean P a z i v ∂Instance.clocksLaw (Finset.univ.erase i).card := by
  let Q := totalEmpiricalInstance (reservoirCoordinates.symm a)
  have hm := measurable_empiricalReverseOtherCandidateLossMean P hP a hz i
  have hp := Instance.restrictClocks_measurePreserving (stateEmbedding (Finset.univ.erase i))
  have hFull := (canonical_arrivalLoss_candidate_integral P Q hP (totalEmpiricalInstance_integrable _) z hz i).1
  have hComp : Integrable (fun u => empiricalReverseOtherCandidateLossMean P a z i (u ∘ stateEmbedding (Finset.univ.erase i)))
      (Instance.clocksLaw n) := hFull.congr (Eventually.of_forall fun u => candidateLossMean_true_empirical_eq_sampleAverage P hP a hz i u)
  have hI := (integrable_map_measure (μ:=Instance.clocksLaw n) hm.aestronglyMeasurable hp.measurable.aemeasurable).mpr hComp
  rw [hp.map_eq] at hI
  have he := integral_map (μ:=Instance.clocksLaw n) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  refine ⟨hI,?_⟩
  calc
    _ = ∫ u : Fin n → ℝ, empiricalReverseOtherCandidateLossMean P a z i (u ∘ stateEmbedding (Finset.univ.erase i)) ∂Instance.clocksLaw n :=
      integral_congr_ae (Eventually.of_forall fun u => candidateLossMean_true_empirical_eq_sampleAverage P hP a hz i u)
    _ = _ := he.symm

end ProphetSecretary.Model
