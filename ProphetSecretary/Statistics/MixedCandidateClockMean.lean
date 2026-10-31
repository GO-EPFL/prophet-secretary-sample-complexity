import ProphetSecretary.Statistics.MixedCandidateFactorization
import ProphetSecretary.Statistics.MixedSelectedCandidateContribution
import ProphetSecretary.Statistics.CanonicalLossEvaluation

/-!
# Actual full and other-clock means in both mixed directions

Both directions use the TRUE candidate marginal. In reverse mode only the
Bellman target changes to the mixed design; the online offers remain true.
Proved canonical value-invariance and exact known-label restriction remove the
candidate's unused clock by an actual uniform-product projection.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

noncomputable def mixedFullCandidateLossMean (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    (a : (Fin n × Fin k) → ℝ) (z : ℝ) (hz : 0≤z) (reverse : Bool) (i : Fin n) (u : Fin n → ℝ) : ℝ :=
  if reverse then candidateLossMeanUnder P (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) P hP z hz i u
  else candidateLossMean (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) P
    (mixedEmpiricalInstance_integrable P hP known _) z hz i u

lemma mixedFullCandidateLossMean_eq_otherMean (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) (reverse : Bool) (i : Fin n) (u : Fin n → ℝ) :
    mixedFullCandidateLossMean P hP known a z hz reverse i u =
      mixedOtherCandidateLossMean P known a z reverse i (u ∘ stateEmbedding (Finset.univ.erase i)) := by
  cases reverse
  · unfold mixedFullCandidateLossMean
    simp only [Bool.false_eq_true,↓reduceIte]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun t =>
      mixedCanonicalCandidateLoss_eq_otherLoss P hP known a hz i u x t)
  · unfold mixedFullCandidateLossMean
    simp only [↓reduceIte]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun t =>
      trueCanonicalCandidateLoss_mixedTarget_eq_otherLoss P hP known a hz i u x t)

lemma measurable_mixedOtherCandidateLossMean (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) (reverse : Bool) (i : Fin n) :
    Measurable (mixedOtherCandidateLossMean P known a z reverse i) := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  let y := reservoirCoordinates.symm (restrictTrainingCoordinates A a)
  let T := ((Fin A.card → ℝ) × ℝ) × ℝ
  have hL := measurable_mixedClockGapLossDirection (Ω:=T) (P.restrictTo A)
    (P.restrictTo_integrable_maximum A hP) (knownInState known A)
    (y:=fun _ => y) (z:=fun _ => z) (t:=fun q => q.2) (x:=fun q => q.1.2) (u:=fun q => q.1.1)
    (fun _ _ => measurable_const) measurable_const measurable_snd (measurable_snd.comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)) (fun _ => hz) reverse
  have hInner : StronglyMeasurable (fun q : (Fin A.card → ℝ) × ℝ =>
      ∫ t, mixedClockGapLossDirection (P.restrictTo A) (knownInState known A) y z reverse q.1 q.2 t ∂Instance.uniformClock) :=
    hL.stronglyMeasurable.integral_prod_right' (ν:=Instance.uniformClock)
  convert (hInner.integral_prod_right' (ν:=P.law i)).measurable using 1
  funext v
  rfl

theorem mixed_fullCandidateMean_integral_otherClocks (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) (reverse : Bool) (i : Fin n) :
    Integrable (mixedOtherCandidateLossMean P known a z reverse i) (Instance.clocksLaw (Finset.univ.erase i).card) ∧
    (∫ u, mixedFullCandidateLossMean P hP known a z hz reverse i u ∂Instance.clocksLaw n) =
      ∫ v, mixedOtherCandidateLossMean P known a z reverse i v ∂Instance.clocksLaw (Finset.univ.erase i).card := by
  let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm a)
  have hQ := mixedEmpiricalInstance_integrable P hP known (reservoirCoordinates.symm a)
  have hm := measurable_mixedOtherCandidateLossMean P hP known a hz reverse i
  have hp := Instance.restrictClocks_measurePreserving (stateEmbedding (Finset.univ.erase i))
  have hFull : Integrable (mixedFullCandidateLossMean P hP known a z hz reverse i) (Instance.clocksLaw n) := by
    cases reverse
    · exact (canonical_arrivalLoss_candidate_integral Q P hQ hP z hz i).1
    · exact (canonical_arrivalLoss_candidate_integral_under P Q P hP hQ hP z hz i).1
  have hComp : Integrable (fun u => mixedOtherCandidateLossMean P known a z reverse i (u ∘ stateEmbedding (Finset.univ.erase i)))
      (Instance.clocksLaw n) := hFull.congr (Eventually.of_forall fun u => mixedFullCandidateLossMean_eq_otherMean P hP known a hz reverse i u)
  have hI := (integrable_map_measure (μ:=Instance.clocksLaw n) hm.aestronglyMeasurable hp.measurable.aemeasurable).mpr hComp
  rw [hp.map_eq] at hI
  have he := integral_map (μ:=Instance.clocksLaw n) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  refine ⟨hI,?_⟩
  calc
    _ = ∫ u : Fin n → ℝ, mixedOtherCandidateLossMean P known a z reverse i (u ∘ stateEmbedding (Finset.univ.erase i)) ∂Instance.clocksLaw n :=
      integral_congr_ae (Eventually.of_forall fun u => mixedFullCandidateLossMean_eq_otherMean P hP known a hz reverse i u)
    _ = _ := he.symm

end ProphetSecretary.Model
