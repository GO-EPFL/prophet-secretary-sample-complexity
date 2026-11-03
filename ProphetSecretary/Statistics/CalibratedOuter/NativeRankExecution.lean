import ProphetSecretary.Statistics.CalibratedOuter.RationalExecution
import ProphetSecretary.Statistics.CalibratedOuter.FairRankExecution
import ProphetSecretary.Statistics.FiniteBitWork
import ProphetSecretary.Statistics.NativeCalibrationDecision

/-!
# Native rational execution of the outer rank learner

The rational cutoff and display agree exactly with the real model under
casting. Keeping rank labels while transforming observed values preserves
the legal prefix used by the bounded policy.
-/

open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ}

def outerRawBlocks {K : Type} (y : Fin n → Fin (outerSampleBudget m) → K) :
    (Fin n → Fin m → K) × ((Fin n → Fin (outerPilotRounds m) → K) × (Fin n → Fin (2*m) → K)) :=
  (fun i j => y i (Fin.castAdd (outerPilotRounds m+2*m) j),
   fun i j => y i (Fin.natAdd m (Fin.castAdd (2*m) j)),
   fun i j => y i (Fin.natAdd m (Fin.natAdd (outerPilotRounds m) j)))

lemma outerRawBlocks_real (y : Reservoir n (outerSampleBudget m)) :
    outerRawBlocks y=outerReservoirBlocks n m y := rfl

private lemma nativeMarkDecode (b : ℕ) (bits : Fin b → Bool) :
    ((countedStoredDyadicUniform b bits).1 : ℝ)=gridPoint (2^b) (fairBitsIndex b bits) := by
  simp only [countedStoredDyadicUniform_value,countedDyadicUniform,countedFairBitsIndex_value,gridPoint_ratCast]

private lemma vector_get_ofFn {A : Type*} {N : ℕ} (f : Fin N → A) (j : Fin N) :
    (Vector.ofFn f).get j=f j := Vector.getElem_ofFn j.isLt

lemma countedOuterHistory_rankCast (H : ℚ) (cutoff : ℚ × ℚ) (tags : Fin n → ℚ)
    (hist : Fin n → Option (Fin n × ℚ)) :
    calibrationRankHistoryCast (countedOuterHistory m H cutoff tags hist).1 =
      transformRankHistory (fun j x => outerMeshDisplay m (H : ℝ)
        (retainAboveTag (castOuterPair cutoff) (x,(tags j : ℝ)))) (calibrationRankHistoryCast hist) := by
  funext j
  simp only [countedOuterHistory,vector_get_ofFn,calibrationRankHistoryCast,transformRankHistory]
  cases e : hist j with
  | none => rfl
  | some a =>
    obtain ⟨k,x⟩ := a
    simp only [Option.map_some]
    rw [← countedDisplay_ratCast m H cutoff (x,tags j), countedDisplay_value]
    rfl

lemma countedOuterHistory_rank (H : ℚ) (cutoff : ℚ × ℚ) (tags : Fin n → ℚ)
    (hist : Fin n → Option (Fin n × ℚ)) (i : Fin n) :
    onlineQueryRank (countedOuterHistory m H cutoff tags hist).1 i=onlineQueryRank hist i := by
  unfold onlineQueryRank
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,countedOuterHistory,vector_get_ofFn]
  cases hist j <;> rfl

lemma outerFairRankLearner_decide (hm : 1≤m) (L : RankLearner n (2*m)) (b : ℕ)
    (y : Reservoir n (outerSampleBudget m)) (marks : OuterMarkArray n m (Fin b → Bool)) (s : L.Seed)
    (k i : Fin n) (x : ℝ) (H : RankHistory n) :
    (outerFairRankLearner hm L b).policy.decide (y,marks,s) k i x H =
      (outerRankPolicy m hm L).decide
        (y,outerSeedFromMarks L.rankToClock (unpackOuterMarks (fairMarkDecoder b marks)) s) k i x H := by
  change (outerRankPolicy m hm L).decide
    (decodedReservoir (trainingTranscript (firstAvailableRequest (outerSampleBudget m)) (marks,s) y),
      outerSeedFromMarks L.rankToClock (unpackOuterMarks (fairMarkDecoder b marks)) s) k i x H=_
  rw [decodedReservoir_firstAvailable_transcript]

/-- The native outer decision is exactly the real rank policy once the
native bounded decision is identified on its transformed input. -/
theorem countedFiniteOuterDecision_eq_of_inner (hm : 1≤m) (T P : FairCallSchedule) (b c o : ℕ)
    (mu zlo zhi Lbar : ℚ) (L : RankLearner n (2*m))
    (y : Fin n → Fin (outerSampleBudget m) → ℚ)
    (marks : OuterMarkArray n m (Fin o → Bool))
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n)) (seed : L.Seed)
    (hInner : ∀ (d : Fin n → Fin (2*m) → ℚ) (k i : Fin n) (x : ℚ)
      (H : Fin n → Option (Fin n × ℚ)), onlineQueryRank H i=k →
      (countedFiniteCalibrationDecision P zlo zhi
        (countedFiniteCalibrationPrepare T P b c mu zlo zhi Lbar
          (fun i j => d i (finiteTrainingIndex m j)) (fun j i => d i (finiteValidationIndex m j)) bits)
        i x H).1 =
      L.policy.decide ((fun i j => (d i j : ℝ)),seed) k i (x : ℝ) (calibrationRankHistoryCast H))
    (k i : Fin n) (x : ℚ) (H : Fin n → Option (Fin n × ℚ)) (hRank : onlineQueryRank H i=k) :
    let Y := outerRawBlocks y
    let q := countedFiniteOuterPrepare hm T P b c o mu zlo zhi Lbar
      (fun r i => Y.1 i r) (fun r i => Y.2.1 i r) (fun r i => Y.2.2 i r) marks bits
    (countedFiniteOuterDecision P zlo zhi q k i x H).1 =
      (outerFairRankLearner hm L o).policy.decide ((fun i j => (y i j : ℝ)),marks,seed)
        k i (x : ℝ) (calibrationRankHistoryCast H) := by
  dsimp only
  let Y := outerRawBlocks y
  let tags := (countedFiniteOuterMarks o marks).1
  let u := unpackOuterMarks (fairMarkDecoder o marks)
  let yR : Reservoir n (outerSampleBudget m) := fun i j => (y i j : ℝ)
  let p : OuterLearnerInput m L.rankToClock := (yR,outerSeedFromMarks L.rankToClock u seed)
  let cut := fun r i => (Y.1 i r,tags.1 r i)
  let pilot := fun r i => (Y.2.1 i r,tags.2.1 r i)
  let inner := fun r i => (Y.2.2 i r,tags.2.2.1 r i)
  let q := countedOuterPrepare hm cut pilot inner
  let R := preparedOuterInput m hm L.rankToClock p
  have hTags : u =
      (fun r i => (tags.1 r i : ℝ),fun r i => (tags.2.1 r i : ℝ),
        fun r i => (tags.2.2.1 r i : ℝ),fun i => (tags.2.2.2 i : ℝ)) := by
    have hFun : fairMarkDecoder o marks =
        fun j => ((countedStoredDyadicUniform o (marks j)).1 : ℝ) := by
      funext j
      exact (nativeMarkDecode o (marks j)).symm
    unfold u
    rw [hFun]
    simp only [tags,countedFiniteOuterMarks,vector_get_ofFn,unpackOuterMarks]
  have hR : R=countedOuterPrepare hm (fun r i => castOuterPair (cut r i))
      (fun r i => castOuterPair (pilot r i)) (fun r i => castOuterPair (inner r i)) := by
    change countedOuterPrepare hm
      (fun r i => ((outerReservoirBlocks n m yR).1 i r,u.1 r i))
      (fun r i => ((outerReservoirBlocks n m yR).2.1 i r,u.2.1 r i))
      (fun r i => ((outerReservoirBlocks n m yR).2.2 i r,u.2.2.1 r i)) = _
    rw [← outerRawBlocks_real,hTags]
    rfl
  have hCast := countedOuterPrepare_ratCast hm cut pilot inner
  dsimp only at hCast
  have hCut : R.cutoff=castOuterPair q.cutoff := by rw [hR]; exact hCast.1
  have hPilot : R.pilot=(q.pilot : ℝ) := by rw [hR]; exact hCast.2.1
  have hData : R.displayed=(fun i j => (q.displayed i j : ℝ)) := by
    rw [hR]
    exact hCast.2.2
  rw [outerFairRankLearner_decide]
  change _=(outerRankPolicy m hm L).decide p k i (x : ℝ) (calibrationRankHistoryCast H)
  have hp : outerPilotAt m hm L.rankToClock p=(q.pilot : ℝ) :=
    (preparedOuterInput_pilot m hm L.rankToClock p).symm.trans hPilot
  have hc : outerCutoffAt m hm L.rankToClock p=castOuterPair q.cutoff :=
    (preparedOuterInput_cutoff m hm L.rankToClock p).symm.trans hCut
  have ht (j : Fin n) : outerOnlineTags m L.rankToClock p j=(tags.2.2.2 j : ℝ) := by
    change u.2.2.2 j=_
    rw [hTags]
  by_cases hq : q.pilot=0
  · have h0 : outerPilotAt m hm L.rankToClock p=0 := by rw [hp,hq]; norm_num
    unfold countedFiniteOuterPrepare
    dsimp only
    rw [if_pos hq]
    change (countedOuterOnline q tags.2.2.2 (fun _ _ _ _ => (false,1)) k i x H).1=_
    rw [countedOuterOnline,if_pos hq]
    simp only [outerRankPolicy,if_pos h0,outerRetainedObservation,hc,ht]
    rw [← countedRetention_value]
    change decide (0<countedRetention q.cutoff (x,tags.2.2.2 i)) =
      decide (0<countedRetention (castOuterPair q.cutoff) (castOuterPair (x,tags.2.2.2 i)))
    rw [countedRetention_ratCast]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Rat.cast_pos]
  · have h0 : outerPilotAt m hm L.rankToClock p≠0 := by rw [hp]; exact_mod_cast hq
    let S := 1000*q.pilot
    let V := countedDisplay m S q.cutoff (x,tags.2.2.2 i)
    let hist := countedOuterHistory m S q.cutoff tags.2.2.2 H
    have hT : outerInnerTraining m hm L.rankToClock p=(fun i j => (q.displayed i j : ℝ)) :=
      (preparedOuterInput_displayed m hm L.rankToClock p h0).symm.trans hData
    have hf : (1000 : ℝ)*outerPilotAt m hm L.rankToClock p=(S : ℝ) := by rw [hp]; simp [S]
    have hV : (V.1 : ℝ)=outerDisplayedObservation m hm L.rankToClock p i (x : ℝ) := by
      have h := countedDisplay_ratCast m S q.cutoff (x,tags.2.2.2 i)
      rw [countedDisplay_value] at h
      rw [outerDisplayedObservation,outerRetainedObservation,hf,hc,ht]
      exact h.symm
    have hH : calibrationRankHistoryCast hist.1=transformRankHistory
        (outerDisplayedObservation m hm L.rankToClock p) (calibrationRankHistoryCast H) := by
      have h : outerDisplayedObservation m hm L.rankToClock p = fun j y =>
          outerMeshDisplay m (S : ℝ) (retainAboveTag (castOuterPair q.cutoff) (y,(tags.2.2.2 j : ℝ))) := by
        funext j y
        rw [outerDisplayedObservation,outerRetainedObservation,hf,hc,ht]
      rw [countedOuterHistory_rankCast,h]
    have hRank' : onlineQueryRank hist.1 i=k := (countedOuterHistory_rank S q.cutoff _ H i).trans hRank
    have he := hInner q.displayed k i V.1 hist.1 hRank'
    unfold countedFiniteOuterPrepare
    dsimp only
    rw [if_neg hq]
    let Q := countedFiniteCalibrationPrepare T P b c mu zlo zhi Lbar
      (fun i j => q.displayed i (finiteTrainingIndex m j))
      (fun j i => q.displayed i (finiteValidationIndex m j)) bits
    change (countedOuterOnline q tags.2.2.2
      (fun (_ : Fin n) j y H => countedFiniteCalibrationDecision P zlo zhi Q j y H) k i x H).1 = _
    rw [countedOuterOnline,if_neg hq]
    simp only [outerRankPolicy,if_neg h0]
    rw [hT,← hV,← hH]
    exact he

end ProphetSecretary.Statistics.Calibration
