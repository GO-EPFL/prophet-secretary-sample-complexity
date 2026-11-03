import ProphetSecretary.Statistics.ArithmeticLearningBounds
import ProphetSecretary.Statistics.ArithmeticCalibrationTapes
import ProphetSecretary.Statistics.CalibrationRankRandomness

/-!
# Total arithmetic work

The independent uniform arrays are allocated before the validation
and online decisions. The allocation and execution bounds hold for
every outcome and use the same public scales.
-/

open Set
open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ}

structure ArithmeticCalibrationAux (n m J CT RT CP RP : ℕ) (K : Type) where
  banks : CalibrationQueryArrays n m J (ArithmeticSeedBank n CT RT K) (ArithmeticSeedBank n CP RP K)
  clocks : Fin m → Fin n → K
  coin : K
  work : ℕ

universe v

def sampleArithmeticCalibrationAuxM {M : Type → Type v} [Monad M] {K : Type}
    (n m J CT RT CP RP : ℕ) (uniform : M K) : M (ArithmeticCalibrationAux n m J CT RT CP RP K) := do
  let bank ← sampleArithmeticCalibrationQueryTapesM n m J CT RT CP RP uniform
  let clocks ← sampleArithmeticValidationClocksM n m uniform
  let coin ← uniform
  pure ⟨bank.1,clocks.1,coin,bank.2+clocks.2+4⟩

private lemma auxCounter_bind {A B : Type} (x : StateM ℕ A) (f : A → StateM ℕ B) (c : ℕ) :
    (x >>= f).run c = (f (x.run c).1).run (x.run c).2 := by
  change (let (a,s) := x.run c; (f a).run s) = _
  cases x.run c
  rfl

private lemma auxCounter_pure {A : Type} (x : A) (c : ℕ) :
    (pure x : StateM ℕ A).run c = (x,c) := rfl

theorem sampleArithmeticCalibrationAuxM_counter {K : Type} (n m J CT RT CP RP : ℕ)
    (uniform : StateM ℕ K) (h : ∀ c, (uniform.run c).2 = c+1) (c : ℕ) :
    ((sampleArithmeticCalibrationAuxM n m J CT RT CP RP uniform).run c).2 =
      c+(4*m+1)*(multilevelBankSlots CT RT*(3*n+2))+
        arithmeticContinuationTapeCount n m J*(multilevelBankSlots CP RP*(3*n+2))+m*n+1 := by
  simp only [sampleArithmeticCalibrationAuxM, auxCounter_bind, auxCounter_pure, h,
    sampleArithmeticCalibrationQueryTapesM_counter _ _ _ _ _ _ _ _ h,
    sampleArithmeticValidationClocksM_counter _ _ _ h]

def arithmeticCalibrationAuxBound (n m J CT RT CP RP : ℕ) : ℕ :=
  (4*m+1)*arithmeticPlannerBankAllocationBound n CT RT+
    arithmeticContinuationTapeCount n m J*arithmeticPlannerBankAllocationBound n CP RP+
    10*((4*m+1)+arithmeticContinuationTapeCount n m J+1)+6+(m*(5*n+8)+6)+4

theorem sampleArithmeticCalibrationAuxM_work {K : Type} (n m J CT RT CP RP : ℕ)
    (uniform : StateM ℕ K) (c : ℕ) :
    ((sampleArithmeticCalibrationAuxM n m J CT RT CP RP uniform).run c).1.work ≤
      arithmeticCalibrationAuxBound n m J CT RT CP RP := by
  simp only [sampleArithmeticCalibrationAuxM, auxCounter_bind, auxCounter_pure,
    sampleArithmeticValidationClocksM_work, arithmeticCalibrationAuxBound]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (sampleArithmeticCalibrationQueryTapesM_work _ _ _ _ _ _ _ uniform c) _) _

lemma arithmeticPlannerBankAllocationBound_le_full (n m C R : ℕ) :
    arithmeticPlannerBankAllocationBound n C R≤20*calibrationFullQueryBound n m R C := by
  refine (arithmeticPlannerBankAllocationBound_le n C R).trans ?_
  have h : 450*(R+1)^4+15*C*16^R+5*C*16^R*(3*n+2)≤calibrationFullQueryBound n m R C := by
    unfold calibrationFullQueryBound
    omega
  exact (Nat.mul_le_mul_left 12 h).trans (Nat.mul_le_mul_right _ (by decide))

lemma arithmeticCalibrationAuxBound_polynomial {CT RT CP RP : ℕ} {K : ℝ}
    (hJ : J≤m) (hK : 0≤K)
    (hT : (calibrationFullQueryBound n m RT CT : ℝ)≤K*((n:ℝ)+m+2)^291)
    (hP : (calibrationFullQueryBound n m RP CP : ℝ)≤K*((n:ℝ)+m+2)^291) :
    (arithmeticCalibrationAuxBound n m J CT RT CP RP : ℝ)≤100*(K+1)*((n:ℝ)+m+2)^295 := by
  let N := (n:ℝ)+m+2
  let T := (4*m+1 : ℕ)
  let P := arithmeticContinuationTapeCount n m J
  let BT := arithmeticPlannerBankAllocationBound n CT RT
  let BP := arithmeticPlannerBankAllocationBound n CP RP
  have hn0 : 0≤(n:ℝ) := Nat.cast_nonneg n
  have hm0 : 0≤(m:ℝ) := Nat.cast_nonneg m
  have hN : 1≤N := by dsimp [N]; linarith only [hn0,hm0]
  have hn : (n:ℝ)≤N := by dsimp [N]; linarith only [hn0,hm0]
  have hm : (m:ℝ)≤N := by dsimp [N]; linarith only [hn0,hm0]
  have hm1 : (m:ℝ)+1≤N := by dsimp [N]; linarith only [hn0,hm0]
  have hJ1 : (J:ℝ)+1≤N := by
    have h : (J:ℝ)≤m := by exact_mod_cast hJ
    exact (add_le_add h (show (1:ℝ)≤1 from le_rfl)).trans hm1
  have hB1 : (BT:ℝ)≤20*(K*N^291) := by
    have h := arithmeticPlannerBankAllocationBound_le_full n m CT RT
    have hc : (BT:ℝ)≤20*(calibrationFullQueryBound n m RT CT:ℝ) := by exact_mod_cast h
    exact hc.trans
      (mul_le_mul_of_nonneg_left hT (by norm_num))
  have hB2 : (BP:ℝ)≤20*(K*N^291) := by
    have h := arithmeticPlannerBankAllocationBound_le_full n m CP RP
    have hc : (BP:ℝ)≤20*(calibrationFullQueryBound n m RP CP:ℝ) := by exact_mod_cast h
    exact hc.trans
      (mul_le_mul_of_nonneg_left hP (by norm_num))
  have h13 : N≤N^3 := by simpa only [pow_one] using pow_le_pow_right₀ hN (by decide : 1≤3)
  have hSlots : (T:ℝ)+(P:ℝ)≤5*N^3 := by
    have ht : (T:ℝ)≤4*N := by dsimp [T,N]; push_cast; linarith only [hn0,hm0]
    have hp : (P:ℝ)≤N^3 := by
      dsimp [P,arithmeticContinuationTapeCount]
      push_cast
      rw [pow_succ,pow_two]
      simpa only [mul_assoc] using
        mul_le_mul hm1 (mul_le_mul hn hJ1 (by positivity) (by positivity))
          (by positivity) (by linarith only [hN])
    linarith only [ht,hp,h13]
  have hSum : (T:ℝ)*BT+(P:ℝ)*BP ≤ 100*K*N^294 := by
    calc
      _ ≤ (T:ℝ)*(20*(K*N^291))+(P:ℝ)*(20*(K*N^291)) :=
        add_le_add (mul_le_mul_of_nonneg_left hB1 (by positivity)) (mul_le_mul_of_nonneg_left hB2 (by positivity))
      _ = ((T:ℝ)+(P:ℝ))*(20*(K*N^291)) := (add_mul _ _ _).symm
      _ ≤ (5*N^3)*(20*(K*N^291)) := mul_le_mul_of_nonneg_right hSlots (by positivity)
      _ = _ := by
        rw [show (294:ℕ)=3+291 by decide,pow_add,show (100:ℝ)=5*20 by norm_num]
        ac_rfl
  have hN3 : 1≤N^3 := one_le_pow₀ hN
  have hN2 : N^2≤N^3 := pow_le_pow_right₀ hN (by decide)
  have h3 : N^3≤N^294 := pow_le_pow_right₀ hN (by decide)
  have h4 : N^294≤N^295 := pow_le_pow_right₀ hN (by decide)
  have hClock : (m:ℝ)*(5*(n:ℝ)+8)+6≤19*N^3 := by
    calc
      _ ≤ N*(5*N+8)+6 := by
        have he : 5*(n:ℝ)+8≤5*N+8 := by linarith only [hn]
        exact add_le_add (mul_le_mul hm he (by positivity) (by linarith only [hN])) le_rfl
      _ = 5*N^2+8*N+6 := by ring
      _ ≤ _ := by linarith only [hN2,h13,hN3]
  have hAux : 10*((T:ℝ)+(P:ℝ)+1)+6+((m:ℝ)*(5*(n:ℝ)+8)+6)+4 ≤ 89*N^3 := by
    linarith only [hSlots,hClock,hN3]
  change ((T*BT+P*BP+10*(T+P+1)+6+(m*(5*n+8)+6)+4 : ℕ):ℝ)≤_
  push_cast
  calc
    _ ≤ 100*K*N^294+89*N^294 := by
      rw [show (T:ℝ)*BT+(P:ℝ)*BP+10*((T:ℝ)+(P:ℝ)+1)+6+((m:ℝ)*(5*(n:ℝ)+8)+6)+4 =
        ((T:ℝ)*BT+(P:ℝ)*BP)+(10*((T:ℝ)+(P:ℝ)+1)+6+((m:ℝ)*(5*(n:ℝ)+8)+6)+4) by ac_rfl]
      exact add_le_add hSum (hAux.trans (mul_le_mul_of_nonneg_left h3 (by norm_num)))
    _ ≤ 100*(K+1)*N^294 := by
      rw [mul_add,mul_one,add_mul]
      have h89 : (89:ℝ)*N^294≤100*N^294 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      exact add_le_add le_rfl h89
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

end ProphetSecretary.Statistics.Calibration
