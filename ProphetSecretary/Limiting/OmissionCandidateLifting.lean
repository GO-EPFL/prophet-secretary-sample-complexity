import ProphetSecretary.Limiting.OmissionPointLifting
import ProphetSecretary.Limiting.CountablePairEvents
import ProphetSecretary.Limiting.HybridPositivePairBranch

/-!
# Retained positive occurrences lift to the genuine hybrid execution

The correspondence preserves physical time and value. Distinct old arrivals
remain distinct by the actual clock injectivity event, including arrivals of
individuals whose realized values are zero.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

lemma omission_candidate_lift (B : CountableInstance) {Seed : Type*}
    (N : ℕ) (q : OmissionExecutionWorld Seed) {cut : ℝ}
    (hCount : bandCountingMeasure q.1.2=joinedCloud q.1.1)
    (hLow : LowCloudRegular B cut q.1.1.2)
    (hHigh : ∀ j : Fin q.1.1.1.1, cut < (q.1.1.1.2 j).2)
    (i : Candidate) (hPrefix : candidatePrefixLevel i ≤ N)
    (hPresent : candidatePresent (oldExecutionWorld q) i)
    (hValue : cut < (candidatePoint (oldExecutionWorld q) i).2) :
    ∃ l : Fin (N+q.1.1.1.1),
      (combinedClocks (newExecutionWorld N q).2.2.1 (newExecutionWorld N q).1.2 l,
        combinedValues (newExecutionWorld N q).2.1 (newExecutionWorld N q).1.2 l)=
          candidatePoint (oldExecutionWorld q) i := by
  cases i with
  | inl i =>
    have hi : i < N := Nat.lt_of_succ_le hPrefix
    refine ⟨(⟨i,hi⟩ : Fin N).castAdd q.1.1.1.1,?_⟩
    simp only [combinedClocks,combinedValues,Fin.addCases_left,newExecutionWorld,
      omissionNewWorld,splitIndividualsWorld,splitCoordinates,oldExecutionWorld,candidatePoint]
  | inr kj =>
    have hj : kj.2 < (q.1.2 kj.1).1 := hPresent
    have hx : cut < ((q.1.2 kj.1).2 ⟨kj.2,hj⟩).2 := by
      simpa only [oldExecutionWorld,candidatePoint,configurationPoint,dif_pos hj] using hValue
    obtain ⟨l,hl⟩ := omission_high_point_lift B q hCount hLow hHigh kj.1 ⟨kj.2,hj⟩ hx
    refine ⟨l.natAdd N,?_⟩
    simp only [newExecutionWorld,omissionNewWorld,combinedClocks,combinedValues,Fin.addCases_right]
    change ((q.1.1.1.2 l).1,(q.1.1.1.2 l).2)=configurationPoint kj.2 (q.1.2 kj.1)
    rw [hl]
    simp only [configurationPoint,dif_pos hj]

lemma omission_prefix_pair_implies_hybrid_pair (B : CountableInstance) {Seed : Type*}
    (N : ℕ) (q : OmissionExecutionWorld Seed) {cut b η : ℝ} (hcut : cut < b)
    (hCount : bandCountingMeasure q.1.2=joinedCloud q.1.1)
    (hLow : LowCloudRegular B cut q.1.1.2)
    (hHigh : ∀ j : Fin q.1.1.1.1, cut < (q.1.1.1.2 j).2)
    (hInjective : Set.InjOn (fun i => (candidatePoint (oldExecutionWorld q) i).1)
      {i | candidatePresent (oldExecutionWorld q) i})
    (hPair : oldExecutionWorld q ∈ prefixClosePositivePair N b η) :
    newExecutionWorld N q ∈ hybridClosePositivePair b η := by
  obtain ⟨i,j,hIndex,hi,hj,hbi,hbj,hTime⟩ := hPair
  obtain ⟨ki,hki⟩ := omission_candidate_lift B N q hCount hLow hHigh i hIndex.1 hi (hcut.trans hbi)
  obtain ⟨kj,hkj⟩ := omission_candidate_lift B N q hCount hLow hHigh j hIndex.2.1 hj (hcut.trans hbj)
  have hNe : ki ≠ kj := by
    intro he
    have hPoint : candidatePoint (oldExecutionWorld q) i=candidatePoint (oldExecutionWorld q) j := by
      rw [he] at hki
      exact hki.symm.trans hkj
    exact hIndex.2.2 (hInjective hi hj (congrArg Prod.fst hPoint))
  refine ⟨ki,kj,hNe,?_,?_,?_⟩
  · rw [show combinedValues (newExecutionWorld N q).2.1 (newExecutionWorld N q).1.2 ki=
      (candidatePoint (oldExecutionWorld q) i).2 from congrArg Prod.snd hki]
    exact hbi
  · rw [show combinedValues (newExecutionWorld N q).2.1 (newExecutionWorld N q).1.2 kj=
      (candidatePoint (oldExecutionWorld q) j).2 from congrArg Prod.snd hkj]
    exact hbj
  · rw [show combinedClocks (newExecutionWorld N q).2.2.1 (newExecutionWorld N q).1.2 ki=
      (candidatePoint (oldExecutionWorld q) i).1 from congrArg Prod.fst hki,
      show combinedClocks (newExecutionWorld N q).2.2.1 (newExecutionWorld N q).1.2 kj=
      (candidatePoint (oldExecutionWorld q) j).1 from congrArg Prod.fst hkj]
    exact hTime

end ProphetSecretary.Limiting
