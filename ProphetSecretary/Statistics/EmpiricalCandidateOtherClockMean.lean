import ProphetSecretary.Statistics.CandidateGapFactorization
import ProphetSecretary.Statistics.EmpiricalClockGapLoss

/-!
# Candidate loss means use only the other arrival clocks

The empirical continuation and true continuation both exclude the candidate.
Projection of the uniform clock product therefore removes its unused clock
coordinate exactly. This places the local loss in the other-instance product
space used by the uniform regional estimates.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def empiricalOtherCandidateLossMean (P : Instance n) (a : (Fin n × Fin k) → ℝ)
    (z : ℝ) (i : Fin n) (v : Fin (Finset.univ.erase i).card → ℝ) : ℝ :=
  ∫ x, (∫ t, empiricalClockGapLoss (P.restrictTo (Finset.univ.erase i))
    (reservoirCoordinates.symm (restrictTrainingCoordinates (Finset.univ.erase i) a)) z v x t ∂Instance.uniformClock) ∂P.law i

lemma measurable_empiricalOtherCandidateLossMean (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) (i : Fin n) : Measurable (empiricalOtherCandidateLossMean P a z i) := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  let y := reservoirCoordinates.symm (restrictTrainingCoordinates A a)
  have hL : Measurable (fun q : ((Fin A.card → ℝ) × ℝ) × ℝ =>
      empiricalClockGapLoss (P.restrictTo A) y z q.1.1 q.1.2 q.2) :=
    measurable_empiricalClockGapLoss (P.restrictTo A) (P.restrictTo_integrable_maximum A hP)
      (fun _ _ => measurable_const) measurable_const measurable_snd (measurable_snd.comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)) (fun _ => hz)
  have hInner : Measurable (fun q : (Fin A.card → ℝ) × ℝ =>
      ∫ t, empiricalClockGapLoss (P.restrictTo A) y z q.1 q.2 t ∂Instance.uniformClock) :=
    (hL.stronglyMeasurable.integral_prod_right' (ν:=Instance.uniformClock)).measurable
  exact (hInner.stronglyMeasurable.integral_prod_right' (ν:=P.law i)).measurable

lemma candidateLossMean_empirical_eq_otherMean (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) (i : Fin n) (u : Fin n → ℝ) :
    candidateLossMean (totalEmpiricalInstance (reservoirCoordinates.symm a)) P (totalEmpiricalInstance_integrable _) z hz i u =
      empiricalOtherCandidateLossMean P a z i (u ∘ stateEmbedding (Finset.univ.erase i)) := by
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    apply integral_congr_ae
    exact Eventually.of_forall fun t => empiricalCanonicalCandidateLoss_eq_otherGaps P hP a hz i u x t

/-- Exact removal of the candidate's clock after the actual value/clock
resampling identity; no independence premise is supplied by an interface. -/
theorem empirical_candidateMean_integral_otherClocks (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) (i : Fin n) :
    Integrable (empiricalOtherCandidateLossMean P a z i) (Instance.clocksLaw (Finset.univ.erase i).card) ∧
    (∫ u, candidateLossMean (totalEmpiricalInstance (reservoirCoordinates.symm a)) P (totalEmpiricalInstance_integrable _) z hz i u ∂Instance.clocksLaw n) =
      ∫ v, empiricalOtherCandidateLossMean P a z i v ∂Instance.clocksLaw (Finset.univ.erase i).card := by
  let Q := totalEmpiricalInstance (reservoirCoordinates.symm a)
  have hm := measurable_empiricalOtherCandidateLossMean P hP a hz i
  have hp := Instance.restrictClocks_measurePreserving (stateEmbedding (Finset.univ.erase i))
  have hFull := (canonical_arrivalLoss_candidate_integral Q P (totalEmpiricalInstance_integrable _) hP z hz i).1
  have hComp : Integrable (fun u => empiricalOtherCandidateLossMean P a z i (u ∘ stateEmbedding (Finset.univ.erase i)))
      (Instance.clocksLaw n) := hFull.congr (Eventually.of_forall fun u => candidateLossMean_empirical_eq_otherMean P hP a hz i u)
  have hI := (integrable_map_measure (μ:=Instance.clocksLaw n) hm.aestronglyMeasurable hp.measurable.aemeasurable).mpr hComp
  rw [hp.map_eq] at hI
  have he := integral_map (μ:=Instance.clocksLaw n) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  refine ⟨hI,?_⟩
  calc
    _ = ∫ u : Fin n → ℝ, empiricalOtherCandidateLossMean P a z i (u ∘ stateEmbedding (Finset.univ.erase i)) ∂Instance.clocksLaw n :=
      integral_congr_ae (Eventually.of_forall fun u => candidateLossMean_empirical_eq_otherMean P hP a hz i u)
    _ = _ := he.symm

end ProphetSecretary.Model
