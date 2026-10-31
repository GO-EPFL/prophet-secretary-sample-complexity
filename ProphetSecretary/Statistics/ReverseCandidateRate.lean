import ProphetSecretary.Statistics.ReverseCandidateRestore
import ProphetSecretary.Statistics.CandidateRateIntegration
import ProphetSecretary.Statistics.DataSelectedCandidateRate
import ProphetSecretary.Model.TruncatedReward

/-!
# Fixed-weight reverse candidate rate

The empirical candidate marginal has been restored by actual independent-row
averaging. Applying the reverse clock estimate then gives the same coefficient
as for a sample-selected empirical optimizer, without applying centering to a
sample-selected scalar.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem integral_reverseCandidateContribution_rate (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z lo hi : ℝ}
    (hlo : 0<lo) (hlohi : lo≤hi) (hz : z∈Icc lo hi) (i : Fin n) :
    (∫ a, reverseCandidateContribution P z i a ∂P.trainingCoordinateLaw k) ≤
      empiricalCandidateRegretConstant lo hi * (1+(P.restrictTo (Finset.univ.erase i)).totalFirstMoment)*
        (∫ x, x ∂P.law i)/(k:ℝ) := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  let Q := P.restrictTo A
  let B := empiricalCandidateRegretConstant lo hi*(1+Q.totalFirstMoment)/(k:ℝ)
  have hz0 := (hlo.trans_le hz.1).le
  have hQ : ∀ j, ∀ᵐ x ∂Q.law j, x≤1 := fun j => hbound (stateEmbedding A j)
  have hRate (x : ℝ) (hx : 0≤x) :
      (∫ q, ∫ t, dataSelectedClockLoss Q (fun _ => z) x q t ∂Instance.uniformClock
        ∂(Q.trainingCoordinateLaw k).prod (Instance.clocksLaw A.card))≤B*x ∧
      (∫ q, ∫ t, dataSelectedClockLossReverse Q (fun _ => z) x q t ∂Instance.uniformClock
        ∂(Q.trainingCoordinateLaw k).prod (Instance.clocksLaw A.card))≤B*x := by
    constructor
    · simpa [B,div_mul_eq_mul_div,dataSelectedClockLossDirection] using
        Q.dataSelectedClockLossDirection_rate hQ measurable_const hlo hlohi (fun _ => hz) hx false
    · simpa [B,div_mul_eq_mul_div,dataSelectedClockLossDirection] using
        Q.dataSelectedClockLossDirection_rate hQ measurable_const hlo hlohi (fun _ => hz) hx true
  rw [integral_reverseCandidateContribution_restore P hbound hz0 hz.2 i]
  have h := (Q.integrated_candidateRate hQ measurable_const (fun _ => ⟨hz0,hz.2⟩)
    (P.law i) (P.nonnegative i) (P.integrable_maximum_iff.mp (P.integrable_maximum_of_bounded hbound) i) hRate).2
  exact h.trans_eq (by dsimp [B]; ring)

theorem integral_reverseCandidateContribution_rate_full (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z lo hi : ℝ}
    (hlo : 0<lo) (hlohi : lo≤hi) (hz : z∈Icc lo hi) (i : Fin n) :
    (∫ a, reverseCandidateContribution P z i a ∂P.trainingCoordinateLaw k) ≤
      empiricalCandidateRegretConstant lo hi * (1+P.totalFirstMoment)*(∫ x, x ∂P.law i)/(k:ℝ) := by
  apply (integral_reverseCandidateContribution_rate P hbound hlo hlohi hz i).trans
  have hm : 0≤∫ x, x ∂P.law i := integral_nonneg_of_ae (P.nonnegative i)
  have hK := (empiricalCandidateRegretConstant_positive hlo hlohi).le
  have hS := P.totalFirstMoment_restrictTo_le (Finset.univ.erase i)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl hS) hK) hm

end ProphetSecretary.Model
