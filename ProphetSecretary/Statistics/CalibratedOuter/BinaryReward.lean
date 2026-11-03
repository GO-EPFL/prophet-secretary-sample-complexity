import ProphetSecretary.Statistics.CalibratedOuter.BinaryProgram

/-!
# Binary reward agrees with the native rational reward

The encoding of an observation preserves its rational value. The binary
program's first acceptance therefore receives the original offer, under
the same law of ranks, training observations and fair bits.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Model

namespace FairCalibrationParameters

variable {n m : ℕ}

def encodedRankHistory (p : Equiv.Perm (Fin n)) (x : Fin n → ℚ) (k : Fin n) :
    BinaryOuterHistory n (Fin n) :=
  fun j => (rationalRankHistory p x k j).map (fun r => (r.1,BinaryRational.ofRat r.2))

lemma encodedRankHistory_value (p : Equiv.Perm (Fin n)) (x : Fin n → ℚ) (k : Fin n) :
    binaryOuterHistoryValue (encodedRankHistory p x k)=rationalRankHistory p x k := by
  funext j
  unfold binaryOuterHistoryValue encodedRankHistory
  cases rationalRankHistory p x k j <;> simp

noncomputable def binaryAccepted (a : FairCalibrationParameters n m) (mu zlo : BinaryRational)
    (hz : (zlo.value : ℝ)=a.zlo) (seed : a.NativeOuterSeed zlo.value hz)
    (y : Fin n → Fin (outerSampleBudget m) → ℚ) (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) :
    Finset (Fin n) :=
  let q := a.prepareBinaryProgram mu zlo hz (fun i j => BinaryRational.ofRat (y i j)) seed
  Finset.univ.filter fun i => (a.decideBinaryProgram q (p.symm i) i (BinaryRational.ofRat (x i))
    (encodedRankHistory p x (p.symm i))).1=true

lemma binaryAccepted_eq (a : FairCalibrationParameters n m) (mu zlo : BinaryRational)
    (hz : (zlo.value : ℝ)=a.zlo) (seed : a.NativeOuterSeed zlo.value hz)
    (y : Fin n → Fin (outerSampleBudget m) → ℚ) (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) :
    a.binaryAccepted mu zlo hz seed y x p=a.nativeAccepted mu.value zlo.value hz seed y x p := by
  ext i
  have hr : onlineQueryRank (binaryOuterHistoryValue (encodedRankHistory p x (p.symm i))) i=p.symm i := by
    rw [encodedRankHistory_value]
    exact rationalRankHistory_currentRank p x (p.symm i) i
  have hB := a.decideBinaryProgram_value mu zlo hz
    (fun i j => BinaryRational.ofRat (y i j)) seed (p.symm i) i (BinaryRational.ofRat (x i))
    (encodedRankHistory p x (p.symm i)) hr
  have hN := a.nativeFiniteOuterDecision_eq mu.value zlo.value hz y seed.1 seed.2 (p.symm i) i (x i)
    (rationalRankHistory p x (p.symm i)) (rationalRankHistory_currentRank p x (p.symm i) i)
  dsimp only at hB hN
  rw [encodedRankHistory_value] at hB
  simp only [BinaryRational.ofRat_value] at hB
  simp only [binaryAccepted,nativeAccepted,Finset.mem_filter,Finset.mem_univ,true_and]
  have e := hB.trans hN.symm
  exact ⟨fun h => e.symm.trans h,fun h => e.trans h⟩

noncomputable def binaryReward (a : FairCalibrationParameters n m) (mu zlo : BinaryRational)
    (hz : (zlo.value : ℝ)=a.zlo) (seed : a.NativeOuterSeed zlo.value hz)
    (y : Fin n → Fin (outerSampleBudget m) → ℚ) (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) : ℝ :=
  let A := a.binaryAccepted mu zlo hz seed y x p
  ∑ i : Fin n, if i∈A ∧ (∀ j∈A, p.symm i≤p.symm j) then (x i : ℝ) else 0

theorem binaryReward_eq_nativeReward (a : FairCalibrationParameters n m) (mu zlo : BinaryRational)
    (hz : (zlo.value : ℝ)=a.zlo) (seed : a.NativeOuterSeed zlo.value hz)
    (y : Fin n → Fin (outerSampleBudget m) → ℚ) (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) :
    a.binaryReward mu zlo hz seed y x p=a.nativeReward mu.value zlo.value hz seed y x p := by
  unfold binaryReward nativeReward
  dsimp only
  rw [binaryAccepted_eq]

noncomputable def binaryExpectedReward (a : FairCalibrationParameters n m) (mu zlo : BinaryRational)
    (hz : (zlo.value : ℝ)=a.zlo) (P : RationalOfferInstance n) : ℝ :=
  ∫ w : (Fin n → ℚ) × (Equiv.Perm (Fin n) × ((Fin n → Fin (outerSampleBudget m) → ℚ) × a.NativeOuterSeed zlo.value hz)),
    a.binaryReward mu zlo hz w.2.2.2 w.2.2.1 w.1 w.2.1
      ∂P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod
        ((P.samplesLaw (outerSampleBudget m)).prod (a.nativeOuterSeedLaw zlo.value hz)))

theorem binaryExpectedReward_eq_native (a : FairCalibrationParameters n m) (mu zlo : BinaryRational)
    (hz : (zlo.value : ℝ)=a.zlo) (P : RationalOfferInstance n) :
    a.binaryExpectedReward mu zlo hz P=a.nativeExpectedReward mu.value zlo.value hz P := by
  unfold binaryExpectedReward nativeExpectedReward
  apply integral_congr_ae
  exact ae_of_all _ (fun w => a.binaryReward_eq_nativeReward mu zlo hz w.2.2.2 w.2.2.1 w.1 w.2.1)

end FairCalibrationParameters

/-- The binary execution achieves the sample upper bound on rational offers. -/
theorem binary_finite_bit_sample_upper_bound :
    ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (zInv : ℕ)
      (hInv : 1/((1-(b : ℝ))/(b : ℝ))≤(zInv : ℝ)) (A eps0 : ℝ),
      0<A ∧ 0<eps0 ∧ ∀ eps∈Ioo (0 : ℝ) eps0,
        ∃ (m : ℕ) (hm : 2≤m), (outerSampleBudget m : ℝ)≤A/eps ∧
          ∀ (n : ℕ) (hn : 0<n) (P : RationalOfferInstance n), P.toInstance.HasPositiveFiniteMaximum →
            let a : FairCalibrationParameters n m :=
              ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
            let zlo := BinaryRational.ofRat ((1-b)/b)
            let hz : (zlo.value : ℝ)=a.zlo := by
              simp only [zlo,BinaryRational.ofRat_value,Rat.cast_div,Rat.cast_sub,Rat.cast_one]
              rfl
            (optimalCompetitiveRatio-eps)*P.toInstance.expectedMaximum ≤
              a.binaryExpectedReward (BinaryRational.ofRat (1/10000000)) zlo hz P := by
  obtain ⟨b,hb,zInv,hInv,A,eps0,hA,heps,hBound⟩ := native_finite_bit_sample_upper_bound
  refine ⟨b,hb,zInv,hInv,A,eps0,hA,heps,?_⟩
  intro eps he
  obtain ⟨m,hm,hB,hR⟩ := hBound eps he
  refine ⟨m,hm,hB,?_⟩
  intro n hn P hP
  dsimp only
  rw [FairCalibrationParameters.binaryExpectedReward_eq_native,BinaryRational.ofRat_value]
  let a : FairCalibrationParameters n m :=
    ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
  have hNative (q : ℚ) (e : q=(1-b)/b) (hq : (q : ℝ)=a.zlo) :
      (optimalCompetitiveRatio-eps)*P.toInstance.expectedMaximum ≤ a.nativeExpectedReward (1/10000000) q hq P := by
    subst q
    exact hR n hn P hP
  exact hNative _ (BinaryRational.ofRat_value _) _

end ProphetSecretary.Statistics.Calibration
