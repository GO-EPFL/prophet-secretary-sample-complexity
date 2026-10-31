import ProphetSecretary.Limiting.OmissionAcceptedRelations
import ProphetSecretary.Limiting.OmissionReserveGuarantee
import ProphetSecretary.Limiting.HybridObserverPayoff
import ProphetSecretary.Limiting.PointMeasureClockSupport
import ProphetSecretary.Limiting.FirstPointComparison

/-!
# Pathwise reward and duration errors of the actual omission simulator

Subset eligibility increases the stopping time. A selected old offer above d
is preserved exactly; any omitted selected offer is worth at most d while the
simulator receives at least reserve. Thus reward loss is at most d minus reserve.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

variable {Seed : Type*} [MeasurableSpace Seed]

lemma omission_realized_duration_le (B : CountableInstance) (π : CountableRule Seed) (hπ : π.IsMeasurable) (N : ℕ)
    (q : OmissionExecutionWorld Seed) (hcount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    {b : ℝ} (hlow : LowCloudRegular B b q.1.1.2)
    (hFirst : FirstAcceptance.HasFirstIfAccepted π.codeAccepted codeTime (oldExecutionWorld q))
    (hu : ∀ k, combinedClocks (newExecutionWorld N q).2.2.1 (newExecutionWorld N q).1.2 k ∈ Icc (0 : ℝ) 1) :
    π.realizedDuration (oldExecutionWorld q) ≤ (simulateOmittedRule B π N).realizedDuration (newExecutionWorld N q) := by
  let ψ := simulateOmittedRule B π N
  have hψ := simulateOmittedRule_measurable B π hπ N
  have hOld : FirstPoint.time (omissionOldAccepted π q) = π.realizedDuration (oldExecutionWorld q) :=
    FirstAcceptance.pointMeasure_time_eq hFirst (fun i hi => hi.2.1)
  have hNew : FirstPoint.time (omissionNewAccepted B π N q) = ψ.realizedDuration (newExecutionWorld N q) :=
    ψ.hybridDuration_eq_observable hψ _ hu
  calc
    _ = FirstPoint.time (omissionOldAccepted π q) := hOld.symm
    _ ≤ FirstPoint.time (omissionNewAccepted B π N q) :=
      FirstPoint.time_antitone (omissionNewAccepted_le B π hπ N q hcount hlow)
    _ = _ := hNew

lemma omission_realized_reward_le (B : CountableInstance) (π : CountableRule Seed) (hπ : π.IsMeasurable) (N : ℕ)
    (q : OmissionExecutionWorld Seed) (hcount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    {b d : ℝ} (hlow : LowCloudRegular B b q.1.1.2) (had : (B.terminal : ℝ) ≤ d) (hbd : b ≤ d)
    (hTail : ∀ j, N ≤ j → (oldExecutionWorld q).2.1 j ≤ d)
    (hFirst : FirstAcceptance.HasFirstIfAccepted π.codeAccepted codeTime (oldExecutionWorld q))
    (hOldNN : ∀ i, π.codeAccepted (oldExecutionWorld q) i → 0 ≤ codeValue (oldExecutionWorld q) i)
    (hOldInj : Set.InjOn (codeTime (oldExecutionWorld q)) {i | π.codeAccepted (oldExecutionWorld q) i})
    (hu : ∀ k, combinedClocks (newExecutionWorld N q).2.2.1 (newExecutionWorld N q).1.2 k ∈ Icc (0 : ℝ) 1)
    (hx : ∀ k, 0 ≤ combinedValues (newExecutionWorld N q).2.1 (newExecutionWorld N q).1.2 k)
    (hNewInj : Function.Injective (combinedClocks (newExecutionWorld N q).2.2.1 (newExecutionWorld N q).1.2)) :
    π.realizedReward B.terminal (oldExecutionWorld q) ≤
      (simulateOmittedRule B π N).realizedReward B.terminal (newExecutionWorld N q) + (d-(B.terminal : ℝ)) := by
  let ψ := simulateOmittedRule B π N
  have hψ := simulateOmittedRule_measurable B π hπ N
  have hReserve : (B.terminal : ℝ) ≤ ψ.realizedReward B.terminal (newExecutionWorld N q) :=
    simulateOmittedRule_reward_ge_reserve B π N _ _ _ _
  have hNewRaw : FirstPoint.rawReward B.terminal (omissionNewAccepted B π N q) =
      ψ.realizedReward B.terminal (newExecutionWorld N q) := by
    change FirstPoint.rawReward B.terminal (ψ.acceptedPointMeasure (hybridObserverWorld (newExecutionWorld N q)) : Measure Point) = _
    rw [← FirstPoint.reward_eq_rawReward B.terminal (ψ.acceptedPointMeasure (hybridObserverWorld (newExecutionWorld N q)))]
    exact ψ.hybridReward_eq_observable hψ _ hu hx hNewInj B.terminal
  have hOldRaw : FirstPoint.rawReward B.terminal (omissionOldAccepted π q) =
      π.realizedReward B.terminal (oldExecutionWorld q) :=
    FirstAcceptance.pointMeasure_rawReward_eq B.terminal (A := π.codeAccepted) (u := codeTime) (x := codeValue)
      (ω := oldExecutionWorld q) hFirst (fun i hi => hi.2.1) hOldNN hOldInj
  by_cases he : ∃ i, FirstAcceptance.Earliest π.codeAccepted codeTime (oldExecutionWorld q) i
  · obtain ⟨i,hi⟩ := he
    have hReward : π.realizedReward B.terminal (oldExecutionWorld q) = codeValue (oldExecutionWorld q) i :=
      FirstAcceptance.reward_of_earliest B.terminal hi
    by_cases hlarge : d < codeValue (oldExecutionWorld q) i
    · have ht : FirstPoint.time (omissionOldAccepted π q) = codeTime (oldExecutionWorld q) i :=
        (FirstAcceptance.pointMeasure_time_eq hFirst (fun j hj => hj.2.1)).trans
          (FirstAcceptance.stoppingTime_of_earliest hi)
      have hSlice : (omissionOldAccepted π q).restrict {p : Point | p.1 = FirstPoint.time (omissionOldAccepted π q)} =
          Measure.dirac (FirstPoint.time (omissionOldAccepted π q),codeValue (oldExecutionWorld q) i) := by
        rw [ht]
        exact FirstAcceptance.pointMeasure_firstSlice hi.1 hOldInj
      have hNN : ∀ᵐ p ∂omissionOldAccepted π q, 0 ≤ p.1 :=
        FirstAcceptance.pointMeasure_nonnegative_clocks (A := π.codeAccepted) (u := codeTime) (x := codeValue)
          (ω := oldExecutionWorld q) (fun j hj => hj.2.1.1)
      have hSameRaw := FirstPoint.rawReward_preserved_of_high_restriction B.terminal hNN
        (omissionNewAccepted_le B π hπ N q hcount hlow)
        (omissionNewAccepted_high_eq B π hπ N q hcount hlow had hbd hTail) hlarge (hOldNN i hi.1) hSlice
      have hSame : ψ.realizedReward B.terminal (newExecutionWorld N q) =
          π.realizedReward B.terminal (oldExecutionWorld q) := hNewRaw.symm.trans (hSameRaw.trans hOldRaw)
      rw [hSame]
      exact le_add_of_nonneg_right (sub_nonneg.mpr had)
    · rw [hReward]
      have hsmall : codeValue (oldExecutionWorld q) i ≤ d := not_lt.mp hlarge
      linarith only [hsmall,hReserve]
  · rw [π.no_first_reward B.terminal (oldExecutionWorld q) he]
    exact hReserve.trans (le_add_of_nonneg_right (sub_nonneg.mpr had))

end ProphetSecretary.Limiting
