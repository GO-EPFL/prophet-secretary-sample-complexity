import ProphetSecretary.Statistics.MixedCandidateClockMean
import ProphetSecretary.Statistics.MixedSelectedCandidateRate
import ProphetSecretary.Model.CrossLawBellmanLoss

/-!
# Fixed-scalar true-candidate contributions for mixed design loss

Both directions average the independent TRUE marginal, with the scalar fixed
before training. The reverse bound evaluates the true canonical rule on true
online offers against the mixed Bellman target. Actual reach dropping and
three-law resampling connect this loss to the same candidate rate.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

noncomputable def fixedScalarMixedCandidateContribution (P : Instance n) (known : Finset (Fin n))
    (z : ℝ) (reverse : Bool) (i : Fin n) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  ∫ v, mixedOtherCandidateLossMean P known a z reverse i v ∂Instance.clocksLaw (Finset.univ.erase i).card

lemma integrable_fixedScalarMixedCandidateContribution (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z hi : ℝ} (hz : 0≤z) (hzhi : z≤hi)
    (reverse : Bool) (i : Fin n) :
    Integrable (fixedScalarMixedCandidateContribution (k:=k) P known z reverse i) (P.trainingCoordinateLaw k) := by
  have hI := integrable_mixedSelectedCandidateContribution P known hbound
    (Z:=fun _ : Reservoir n k × Unit => z) measurable_const (fun _ => ⟨hz,hzhi⟩) reverse i (Measure.dirac ())
  change Integrable (fun p : (((Fin n × Fin k) → ℝ) × Unit) =>
    fixedScalarMixedCandidateContribution P known z reverse i p.1) ((P.trainingCoordinateLaw k).prod (Measure.dirac ())) at hI
  exact hI.of_comp_fst (by simp)

theorem sum_integral_fixedScalarMixedCandidateContribution_rate (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z lo hi : ℝ}
    (hlo : 0<lo) (hlohi : lo≤hi) (hz : z∈Icc lo hi) (reverse : Bool) :
    (∑ i : Fin n, ∫ a, fixedScalarMixedCandidateContribution P known z reverse i a ∂P.trainingCoordinateLaw k) ≤
      empiricalCandidateRegretConstant lo hi*P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ) := by
  have h := sum_integral_mixedSelectedCandidateContribution_rate P known hbound
    (Z:=fun _ : Reservoir n k × Unit => z) measurable_const hlo hlohi (fun _ => hz) reverse (Measure.dirac ())
  have he (i : Fin n) :
      (∫ p, mixedSelectedCandidateContribution P known (fun _ : Reservoir n k × Unit => z) reverse i p
        ∂(P.trainingCoordinateLaw k).prod (Measure.dirac ())) =
        ∫ a, fixedScalarMixedCandidateContribution P known z reverse i a ∂P.trainingCoordinateLaw k := by
    change (∫ p : (((Fin n × Fin k) → ℝ) × Unit), fixedScalarMixedCandidateContribution P known z reverse i p.1
      ∂(P.trainingCoordinateLaw k).prod (Measure.dirac ())) = _
    simpa only [probReal_univ,one_smul] using integral_fun_fst (μ:=P.trainingCoordinateLaw k)
      (ν:=Measure.dirac ()) (fixedScalarMixedCandidateContribution P known z reverse i)
  simpa only [he] using h

/-- The actual true-policy mixed-design loss, averaged under the TRUE online
instance, is bounded by true-marginal candidate contributions. -/
theorem trueCanonical_mixedDesignActionLoss_le_candidates (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (a : (Fin n × Fin k) → ℝ)
    {z : ℝ} (hz : 0≤z) :
    (P.valuePolicy hP zero_le_one hz).expectedReachedDesignActionLoss
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)) P 1 z ≤
      ∑ i : Fin n, fixedScalarMixedCandidateContribution P known z true i a := by
  let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm a)
  have hQ := mixedEmpiricalInstance_integrable P hP known (reservoirCoordinates.symm a)
  let π := P.valuePolicy hP zero_le_one hz
  let rule : Policy Unit n := π.rule
  have hd := π.expectedDesignActionLoss_le_sum_arrivalLoss_under Q P hQ hP zero_lt_one hz
  change π.expectedReachedDesignActionLoss Q P 1 z ≤
    ∑ i, ∫ ω : World n Unit, rule.arrivalBellmanLoss Q 1 z ω.2.2 ω.1 ω.2.1 i
      ∂P.worldLaw (Measure.dirac ()) at hd
  apply hd.trans_eq
  apply Finset.sum_congr rfl
  intro i _
  have hUnit : (∫ ω : World n Unit, rule.arrivalBellmanLoss Q 1 z ω.2.2 ω.1 ω.2.1 i ∂P.worldLaw (Measure.dirac ())) =
      ∫ ω : World n Unit, rule.arrivalBellmanLoss Q 1 z () ω.1 ω.2.1 i ∂P.worldLaw (Measure.dirac ()) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by rcases ω with ⟨x,u,r⟩; cases r; rfl
  exact hUnit.trans ((canonical_arrivalLoss_candidate_integral_under P Q P hP hQ hP z hz i).2.trans
    (mixed_fullCandidateMean_integral_otherClocks P hP known a hz true i).2)

end ProphetSecretary.Model
