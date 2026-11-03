import ProphetSecretary.Statistics.ArithmeticLearningWork
import ProphetSecretary.Statistics.CalibratedPolynomialWork

/-!
# A uniform polynomial for the arithmetic execution

The target and continuation call bounds are combined with the
validation and online loop sizes at the public calibration scales.
-/

open Set
open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ}

def arithmeticCalibrationTotalBound (n m J WT WP : ℕ) : ℕ :=
  arithmeticCalibrationPreparationBound n m J WT WP+n*arithmeticCalibrationArrivalBound n m J WP

/-- The work of calibration and all online arrivals has polynomial
overhead beyond the two scalar query work bounds. -/
theorem arithmeticCalibrationTotalBound_le (n m J WT WP : ℕ) (hJ : J≤m) :
    arithmeticCalibrationTotalBound n m J WT WP ≤ 400*(n+m+2)^4*(max WT WP+1) := by
  let N := n+m+2
  let W := max WT WP
  let D := N^4*(W+1)
  have hN : 0<N := by dsimp [N]; omega
  have hn : n≤N := by dsimp [N]; omega
  have hm : m≤N := by dsimp [N]; omega
  have hn1 : n+1≤N := by dsimp [N]; omega
  have hm1 : m+1≤N := by dsimp [N]; omega
  have hm2 : m+2≤N := by dsimp [N]; omega
  have hJ1 : J+1≤N := by dsimp [N]; omega
  have hJ2 : J+2≤N := by dsimp [N]; omega
  have hJ3 : J+3≤2*N := by dsimp [N]; omega
  have hm4 : m+4≤2*N := by dsimp [N]; omega
  have hWT : WT≤W := le_max_left _ _
  have hWP : WP≤W := le_max_right _ _
  have hD : N^4≤D := Nat.le_mul_of_pos_right _ (Nat.succ_pos W)
  have hPow (d : ℕ) (hd : d≤4) : N^d≤D := (Nat.pow_le_pow_right hN hd).trans hD
  have hWeighted (d : ℕ) (hd : d≤4) : N^d*(W+1)≤D :=
    Nat.mul_le_mul_right (W+1) (Nat.pow_le_pow_right hN hd)
  have h0 : 1≤D := by simpa using hPow 0 (by decide)
  have hConst (a : ℕ) : a≤a*D := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left a h0
  have h1 : N≤D := by simpa using hPow 1 (by decide)
  have h2 := hPow 2 (by decide)
  have h3 := hPow 3 (by decide)
  have hw1 : N*(W+1)≤D := by simpa using hWeighted 1 (by decide)
  have hw2 := hWeighted 2 (by decide)
  have hw3 := hWeighted 3 (by decide)
  have hM : 100*(n+1)^2*(m+1)^2≤100*D := by
    calc
      _ ≤ 100*N^2*N^2 := Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn1 _))
        (Nat.pow_le_pow_left hm1 _)
      _ = 100*N^4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hD
  have hP : 26*(n+1)*(m+1)≤26*D := by
    calc
      _ ≤ 26*N*N := Nat.mul_le_mul (Nat.mul_le_mul_left _ hn1) hm1
      _ = 26*N^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  have ht : (4*m+1)*(WT+10)≤40*D := by
    calc
      _ ≤ (4*N)*(10*(W+1)) := Nat.mul_le_mul (by dsimp [N]; omega) (by omega)
      _ = 40*(N*(W+1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hw1
  have hV : m*(n*(n*(m+2)+7+(J+1)*(WP+2))+(J+1)*(12*n+3)+6)≤31*D := by
    calc
      _ ≤ N*(N*(N*N+7+N*(2*(W+1)))+N*(15*N)+6) := by
        exact Nat.mul_le_mul hm (Nat.add_le_add_right (Nat.add_le_add
          (Nat.mul_le_mul hn (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul hn hm2) 7)
            (Nat.mul_le_mul hJ1 (by omega))))
          (Nat.mul_le_mul hJ1 (by omega))) 6)
      _ = N^4+7*N^2+2*(N^3*(W+1))+15*N^3+6*N := by ring
      _ ≤ D+7*D+2*D+15*D+6*D := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add hD (Nat.mul_le_mul_left _ h2)) (Nat.mul_le_mul_left _ hw3))
        (Nat.mul_le_mul_left _ h3)) (Nat.mul_le_mul_left _ h1)
      _ = _ := by ring
  have hk : 10*(m+1)*(J+3)≤20*D := by
    calc
      _ ≤ 10*N*(2*N) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hm1) hJ3
      _ = 20*N^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  have hv : arithmeticValidationProfilesBound n m≤21*D := by
    unfold arithmeticValidationProfilesBound
    calc
      _ ≤ N*(10*N^2+5)+4*N+2 := Nat.add_le_add_right (Nat.add_le_add
        (Nat.mul_le_mul hm (Nat.add_le_add_right (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left hn1 _)) 5)) (Nat.mul_le_mul_left _ hm)) 2
      _ = 10*N^3+9*N+2 := by ring
      _ ≤ 10*D+9*D+2*D := Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left _ h3) (Nat.mul_le_mul_left _ h1)) (hConst _)
      _ = _ := by ring
  have ho : n*arithmeticCalibrationArrivalBound n m J WP≤14*D := by
    unfold arithmeticCalibrationArrivalBound
    calc
      _ ≤ N*(N*(2*N)+10+N*(2*(W+1))) := Nat.mul_le_mul hn
        (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul hn hm4) 10)
          (Nat.mul_le_mul hJ1 (by omega)))
      _ = 2*N^3+10*N+2*(N^2*(W+1)) := by ring
      _ ≤ 2*D+10*D+2*D := Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left _ h3) (Nat.mul_le_mul_left _ h1)) (Nat.mul_le_mul_left _ hw2)
      _ = _ := by ring
  have hs : 8+8*(J+1)+4*(J+2)+15+8*(J+1)+10≤53*D := by
    have ha : J+1≤D := hJ1.trans h1
    have hb : J+2≤D := hJ2.trans h1
    calc
      _ ≤ 8*D+8*D+4*D+15*D+8*D+10*D := by
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (hConst _) (Nat.mul_le_mul_left _ ha))
          (Nat.mul_le_mul_left _ hb)) (hConst _)) (Nat.mul_le_mul_left _ ha)) (hConst _)
      _ = _ := by ring
  rw [Nat.mul_assoc]
  change arithmeticCalibrationTotalBound n m J WT WP≤400*D
  calc
    _ = 100*(n+1)^2*(m+1)^2+26*(n+1)*(m+1)+(4*m+1)*(WT+10)+
      m*(n*(n*(m+2)+7+(J+1)*(WP+2))+(J+1)*(12*n+3)+6)+
      10*(m+1)*(J+3)+arithmeticValidationProfilesBound n m+
      n*arithmeticCalibrationArrivalBound n m J WP+(8+8*(J+1)+4*(J+2)+15+8*(J+1)+10) := by
        unfold arithmeticCalibrationTotalBound arithmeticCalibrationPreparationBound
        ac_rfl
    _ ≤ 100*D+26*D+40*D+31*D+20*D+21*D+14*D+53*D :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hM hP) ht) hV) hk) hv) ho) hs
    _ = 305*D := by ring
    _ ≤ _ := Nat.mul_le_mul_right D (by decide)

theorem arithmeticCalibrationTotalBound_of_query_bounds (n m J WT WP : ℕ) (hJ : J≤m)
    (K : ℝ) (hT : (WT : ℝ)≤K*((n:ℝ)+m+2)^291)
    (hP : (WP : ℝ)≤K*((n:ℝ)+m+2)^291) :
    (arithmeticCalibrationTotalBound n m J WT WP : ℝ)≤400*(K+1)*((n:ℝ)+m+2)^295 := by
  let N := (n:ℝ)+m+2
  have hN : 1≤N := by
    dsimp [N]
    linarith only [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) m]
  have hPow : 1≤N^291 := one_le_pow₀ hN
  have hw' : ((max WT WP : ℕ) : ℝ)≤K*N^291 := by
    rw [Nat.cast_max]
    exact max_le hT hP
  have hW : ((max WT WP : ℕ) : ℝ)+1≤(K+1)*N^291 := by
    rw [add_mul,one_mul]
    exact add_le_add hw' hPow
  calc
    _ ≤ 400*N^4*(((max WT WP : ℕ) : ℝ)+1) := by
      dsimp only [N]
      exact_mod_cast arithmeticCalibrationTotalBound_le n m J WT WP hJ
    _ ≤ 400*N^4*((K+1)*N^291) := mul_le_mul_of_nonneg_left hW (by positivity)
    _ = _ := by
      change 400*N^4*((K+1)*N^291)=400*(K+1)*N^295
      rw [show (295:ℕ)=4+291 by decide,pow_add]
      ac_rfl

noncomputable def arithmeticTargetScale (m : ℕ) (hm : 2≤m) : ArithmeticCalibrationScale :=
  ⟨1/(m : ℝ),1/((m : ℝ)^2*(4*(m : ℝ)+1)),targetAccuracy_mem hm,targetFailure_mem hm⟩

noncomputable def arithmeticThresholdScale (n m J : ℕ) (hn : 0<n) (hm : 2≤m)
    (zlo : ℝ) (hz : zlo∈Ioo (0 : ℝ) (1/4)) : ArithmeticCalibrationScale :=
  ⟨policyAccuracy m zlo,policyFailureBound n m J,policyAccuracy_mem hm hz,policyFailure_mem hn hm⟩

lemma arithmeticCalibrationCallBound_le_full (n m : ℕ) (s : ArithmeticCalibrationScale) :
    arithmeticCalibrationCallBound n m s ≤
      calibrationFullQueryBound n m (calibrationPlannerLevel m s.accuracy)
        (confidenceCopyCount s.failure (exists_confidence_level s.failure_mem.1 s.failure_mem.2)) := by
  unfold arithmeticCalibrationCallBound calibrationFullQueryBound
  omega

/-- Uniform polynomial work of the actual bounded arithmetic calibration,
including the entire online phase, at the public query scales. -/
theorem countedArithmeticTotalWork_polynomial [NeZero m] (hn : 0<n) (hm : 2≤m) (hJ : J≤m)
    (mu zlo zhi : ℝ) (hz : zlo∈Ioo (0 : ℝ) (1/4)) (q : Reservoir n m) (x clocks : Fin m → Fin n → ℝ)
    (banks : CalibrationQueryArrays n m J (ArithmeticCalibrationBank n m (arithmeticTargetScale m hm))
      (ArithmeticCalibrationBank n m (arithmeticThresholdScale n m J hn hm zlo hz)))
    (coin : ℝ) (S : Finset (Fin n)) (t offer : Fin n → ℝ) (H : Fin n → History n) :
    let T := arithmeticTargetScale m hm
    let P := arithmeticThresholdScale n m J hn hm zlo hz
    let prep := countedArithmeticPrepare T P mu zlo zhi q x clocks banks coin
    ((prep.work + (∑ i ∈ S, (countedArithmeticDecision P prep (t i) (offer i) (H i) i banks.2.2).2) : ℕ) : ℝ) ≤
      400*(calibrationWorkConstant zlo+1)*((n:ℝ)+m+2)^295 := by
  dsimp only
  let T := arithmeticTargetScale m hm
  let P := arithmeticThresholdScale n m J hn hm zlo hz
  let WT := arithmeticCalibrationCallBound n m T
  let WP := arithmeticCalibrationCallBound n m P
  have hT : (WT : ℝ) ≤ calibrationWorkConstant zlo*((n:ℝ)+m+2)^291 := by
    have h := arithmeticCalibrationCallBound_le_full n m T
    apply le_trans (Nat.cast_le.mpr h)
    exact calibrationTargetQueryWork_polynomial hm hz.1 _
  have hP : (WP : ℝ) ≤ calibrationWorkConstant zlo*((n:ℝ)+m+2)^291 := by
    have h := arithmeticCalibrationCallBound_le_full n m P
    apply le_trans (Nat.cast_le.mpr h)
    exact calibrationThresholdQueryWork_polynomial hn hm hJ hz _
  have hsum := countedArithmeticTotalWork T P mu zlo zhi q x clocks banks coin S t offer H
  dsimp only at hsum
  have hA := arithmeticCalibrationTotalBound_of_query_bounds n m J WT WP hJ
    (calibrationWorkConstant zlo) hT hP
  exact (Nat.cast_le.mpr hsum).trans hA

end ProphetSecretary.Statistics.Calibration
