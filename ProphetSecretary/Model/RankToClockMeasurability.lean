import ProphetSecretary.Model.RankToClock
import ProphetSecretary.Model.RankMeasurability
import ProphetSecretary.Model.ContinuationTransport

/-!
# Measurability of the rank-to-clock adapter

All ranks are computed from the current observation history alone. Absent
observations are distinguished from observed zero values by their option tag.
The current identity totalizes invalid counts without restricting the original
rank policy or its independent seed space.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ}

lemma measurable_clockHistoryPresent : Measurable (clockHistoryPresent (n:=n)) := by
  rw [measurable_finset_iff]
  intro i
  apply measurableSet_setOf.mp
  simpa only [clockHistoryPresent,Finset.mem_filter,Finset.mem_univ,true_and,Set.preimage_setOf_eq,Set.compl_setOf] using
    (measurableSet_observation_none.preimage (measurable_pi_apply i)).compl

lemma measurable_clockHistoryBefore : Measurable (fun p : History n × ℝ => clockHistoryBefore p.1 p.2) := by
  rw [measurable_finset_iff]
  intro i
  apply measurableSet_setOf.mp
  have hEq : {p : History n × ℝ | i∈clockHistoryBefore p.1 p.2}=
      {p | p.1 i≠none}∩{p | observationTime (p.1 i)<p.2} := by
    ext p
    cases hi : p.1 i with
    | none => simp [clockHistoryBefore,hi,observationTime]
    | some z =>
      rcases z with ⟨t,x⟩
      simp [clockHistoryBefore,hi,observationTime]
  rw [hEq]
  exact (measurableSet_observation_none.compl.preimage ((measurable_pi_apply i).comp measurable_fst)).inter
    (measurableSet_lt (measurable_observationTime.comp ((measurable_pi_apply i).comp measurable_fst)) measurable_snd)

lemma measurable_clockHistoryRank : Measurable (fun p : Fin n × ℕ => clockHistoryRank p.1 p.2) :=
  measurable_of_countable _

lemma measurable_currentRankFromClock : Measurable (fun p : Fin n × History n => currentRankFromClock p.1 p.2) := by
  have hCard : Measurable (fun A : Finset (Fin n) => A.card) := measurable_of_finite _
  exact measurable_clockHistoryRank.comp
    (measurable_fst.prodMk (hCard.comp (measurable_clockHistoryPresent.comp measurable_snd)))

lemma measurable_rankHistoryFromClock : Measurable (fun p : Fin n × History n => rankHistoryFromClock p.1 p.2) := by
  classical
  apply measurable_pi_lambda
  intro j
  rw [measurable_comap_iff]
  let A := Fin n × History n
  have hO : Measurable (fun p : A => p.2 j) := (measurable_pi_apply j).comp measurable_snd
  have hNone : MeasurableSet {p : A | p.2 j=none} := measurableSet_observation_none.preimage hO
  have hTime : Measurable (fun p : A => observationTime (p.2 j)) := measurable_observationTime.comp hO
  have hValue : Measurable (fun p : A => observationValue (p.2 j)) := measurable_observationValue.comp hO
  have hBefore : Measurable (fun p : A => clockHistoryBefore p.2 (observationTime (p.2 j))) :=
    measurable_clockHistoryBefore.comp (measurable_snd.prodMk hTime)
  have hCard : Measurable (fun S : Finset (Fin n) => S.card) := measurable_of_finite _
  have hRank : Measurable (fun p : A => clockHistoryRank p.1 (clockHistoryBefore p.2 (observationTime (p.2 j))).card) :=
    measurable_clockHistoryRank.comp (measurable_fst.prodMk (hCard.comp hBefore))
  have hEncoded : Measurable (fun p : A => if p.2 j=none then (Sum.inl () : Unit ⊕ (Fin n × ℝ)) else
      Sum.inr (clockHistoryRank p.1 (clockHistoryBefore p.2 (observationTime (p.2 j))).card,observationValue (p.2 j))) := Measurable.ite hNone
    (measurable_const : Measurable (fun _ : A => (Sum.inl () : Unit ⊕ (Fin n × ℝ))))
    (measurable_inr.comp (hRank.prodMk hValue))
  convert hEncoded using 1
  funext p
  cases hi : p.2 j <;> simp [rankHistoryFromClock,rankObservationCode,hi,observationTime,observationValue]

variable {Seed : Type*} [MeasurableSpace Seed]

/-- Every measurable general rank policy induces a measurable causal clock policy. -/
theorem RankPolicy.rankToClock_measurable (π : RankPolicy Seed n) (hπ : π.IsMeasurable) :
    π.rankToClock.IsMeasurable := by
  let A := Seed × (ℝ × (Fin n × (ℝ × History n)))
  have hr : Measurable (fun z : A => z.1) := measurable_fst
  have hi : Measurable (fun z : A => z.2.2.1) := by fun_prop
  have hx : Measurable (fun z : A => z.2.2.2.1) := by fun_prop
  have hH : Measurable (fun z : A => z.2.2.2.2) := by fun_prop
  have hRank := measurable_currentRankFromClock.comp (hi.prodMk hH)
  have hPast := measurable_rankHistoryFromClock.comp (hi.prodMk hH)
  exact hπ.comp (hr.prodMk (hRank.prodMk (hi.prodMk (hx.prodMk hPast))))

end ProphetSecretary.Model
