import ProphetSecretary.Statistics.RationalCalibrationPreparation
import ProphetSecretary.Statistics.RationalCalibrationGrid

/-!
# The native prepared online decision

The native executor receives only the current offer and observed rank
prefix. The number of observed identities recovers the current rank;
rounding the mixture probability and casting the threshold arithmetic
preserve the measured rank rule.
-/

open ProphetSecretary.Model

namespace ProphetSecretary.Statistics.Calibration

variable {n m J : ℕ} {PSeed : Type}

def calibrationRankHistoryCast (H : Fin n → Option (Fin n × ℚ)) : RankHistory n :=
  fun i => (H i).map (fun a => (a.1,(a.2 : ℝ)))

lemma onlineQueryRank_rankHistory (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (k i : Fin n) :
    onlineQueryRank (rankHistory p x k) i=k := by
  have h : (Finset.univ.filter (fun j => (rankHistory p x k j).isSome=true))=
      (Finset.univ.filter (fun j => p.symm j<k)) := by
    ext j
    by_cases hj : p.symm j<k <;> simp [rankHistory,hj]
  rw [onlineQueryRank,h,card_filter_permutation_lt,clockHistoryRank_of_fin]

lemma onlineQueryRank_of_cast_rankHistory {H : Fin n → Option (Fin n × ℚ)}
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (k i : Fin n)
    (h : calibrationRankHistoryCast H=rankHistory p x k) : onlineQueryRank H i=k := by
  calc
    onlineQueryRank H i=onlineQueryRank (calibrationRankHistoryCast H) i :=
      (onlineQueryRank_map H (fun a : Fin n × ℚ => (a.1,(a.2 : ℝ))) i).symm
    _ = k := by rw [h,onlineQueryRank_rankHistory]

def rationalMixturePolicyIndex (J k : ℕ) (α c : ℚ) : Fin (J+1) :=
  if c<α then upperPolicyIndex J k else lowerPolicyIndex J k

lemma rationalMixturePolicyIndex_eq (J k : ℕ) (α c : ℚ) :
    rationalMixturePolicyIndex J k α c=mixturePolicyIndex J (k,(α : ℝ)) (c : ℝ) := by
  unfold rationalMixturePolicyIndex mixturePolicyIndex
  dsimp only
  by_cases h : c<α
  · rw [if_pos h,if_pos (Rat.cast_lt.mpr h)]
  · rw [if_neg h,if_neg (fun hh => h (Rat.cast_lt.mp hh))]

open scoped Classical in
theorem countedOnlineCalibrationNativeRank_eq [NeZero m]
    (zlo zhi : ℚ)
    (estimate : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ × ℕ)
    (estimateR : ContinuationEstimator n m PSeed)
    (workR : Finset (Fin n) → ℝ → ℝ → PSeed → ℕ)
    (q : Fin n → Fin m → ℚ) (fallback : Bool)
    (hFallback : fallback=decide (familyFallback (calibrationRowsCast q)))
    (hEst : ∀ A u z r, ((estimate A u z r).1 : ℝ)=
      estimateR (calibrationRowsCast q) A (u : ℝ) (z : ℝ) r)
    (r : PolicyQueryArray n J PSeed) (j : Fin (J+1)) (s : Fin n → ℚ)
    (k i : Fin n) (x : ℚ) (H : Fin n → Option (Fin n × ℚ))
    (hRank : onlineQueryRank H i=k) :
    (countedOnlineCalibrationDecision (storedCalibrationCoefficient J zlo zhi) estimate
      q fallback j (s (onlineQueryRank H i)) x H i r).1 =
      (numericalFamilyPolicy (zlo : ℝ) (zhi : ℝ) estimateR j).clockToRank.decide
        ((fun i => (s i : ℝ)),calibrationRowsCast q,r) k i (x : ℝ) (calibrationRankHistoryCast H) := by
  let qR := calibrationRowsCast q
  let f := fun A u z r => (estimateR qR A u z r,workR A u z r)
  have hf := countedOnlineCalibrationDecision_ratCast (storedCalibrationCoefficient J zlo zhi)
    estimate f hEst q fallback j (s (onlineQueryRank H i)) x H i r
  have hz : (fun l => ((storedCalibrationCoefficient J zlo zhi l : ℚ) : ℝ))=
      familyCoefficient (zlo : ℝ) (zhi : ℝ) J := by
    funext l
    rw [storedCalibrationCoefficient_ratCast,storedCalibrationCoefficient_value]
  rw [hz,hRank,hFallback] at hf
  let H' := calibrationRankHistoryCast H
  have hH :
      countedOnlineCalibrationDecision (familyCoefficient (zlo : ℝ) (zhi : ℝ) J) f
        qR (decide (familyFallback qR)) j (s k : ℝ) (x : ℝ) H i r =
      countedOnlineCalibrationDecision (familyCoefficient (zlo : ℝ) (zhi : ℝ) J) f
        qR (decide (familyFallback qR)) j (s k : ℝ) (x : ℝ) H' i r := by
    unfold countedOnlineCalibrationDecision H' calibrationRankHistoryCast
    rw [onlineContinuationSet_map,onlineQueryRank_map]
  have h := countedOnlineCalibrationRankDecision_eq (zlo : ℝ) (zhi : ℝ) estimateR workR
    qR r j (fun i => (s i : ℝ)) k i (x : ℝ) H'
  calc
    _ = (countedOnlineCalibrationDecision (familyCoefficient (zlo : ℝ) (zhi : ℝ) J) f
        qR (decide (familyFallback qR)) j (s k : ℝ) (x : ℝ) H i r).1 := by rwa [hRank,hFallback]
    _ = _ := (congrArg Prod.fst hH).trans h

end ProphetSecretary.Statistics.Calibration
