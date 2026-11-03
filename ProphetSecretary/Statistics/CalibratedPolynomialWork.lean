import ProphetSecretary.Statistics.CalibratedQueryExecution

/-!
# Polynomial growth of the scalar query work bounds

Only the count cutoff and inverse tolerances enter the exponent. The bound
uses the public maximum recursion level and holds on all seed outcomes.
-/

open Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

lemma calibrationWeightBound_poly (m : ℕ) :
    calibrationWeightBound m ≤ (4 : ℝ)^8*2^32*((m : ℝ)+1)^32 := by
  unfold calibrationWeightBound
  rw [mul_pow,← mul_assoc]
  gcongr
  linarith

lemma calibrationLevel_poly {m : ℕ} [NeZero m] {h A : ℝ} (hh : h∈Ioo (0 : ℝ) 1)
    (_hA : 0≤A) (hInv : h⁻¹≤A*((m : ℝ)+1)^3) :
    (16 : ℝ)^calibrationPlannerLevel m h≤
      (6400 : ℝ)^4*((4 : ℝ)^8*2^32*A)^8*((m : ℝ)+1)^280 := by
  have hb : 0≤calibrationWeightBound m :=
    zero_le_one.trans (calibrationWeightBound_ge_one (m := m))
  have he : calibrationWeightBound m/h≤((4 : ℝ)^8*2^32*A)*((m : ℝ)+1)^35 := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ ((4 : ℝ)^8*2^32*((m : ℝ)+1)^32)*(A*((m : ℝ)+1)^3) :=
        mul_le_mul (calibrationWeightBound_poly m) hInv (inv_pos.mpr hh.1).le (by positivity)
      _ = _ := by
        rw [show (35 : ℕ)=32+3 by decide,pow_add]
        ac_rfl
  calc
    _ ≤ (6400 : ℝ)^4*(calibrationWeightBound m/h)^8 := calibration_level_tree_bound hh
    _ ≤ (6400 : ℝ)^4*(((4 : ℝ)^8*2^32*A)*((m : ℝ)+1)^35)^8 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg hb hh.1.le) he _) (by positivity)
    _ = _ := by
      rw [mul_pow,← pow_mul,show (35 : ℕ)*8=280 by decide]
      ac_rfl

lemma levelAllocator_poly (R : ℕ) : (R+1)^4≤16^R := by
  have hr : R+1≤2^R := Nat.succ_le_of_lt Nat.lt_two_pow_self
  calc
    _ ≤ (2^R)^4 := Nat.pow_le_pow_left hr _
    _ = (16 : ℕ)^R := by rw [← pow_mul,mul_comm,pow_mul]; norm_num

lemma scalarPlannerPrimitiveBound_poly (n m : ℕ) :
    scalarPlannerPrimitiveBound n m≤1250*(n+m+2)^3 := by
  unfold scalarPlannerPrimitiveBound
  have h₁ : (n+1)^3≤(n+m+2)^3 := Nat.pow_le_pow_left (by omega) _
  have h₂ : n+m+1≤(n+m+2)^3 := by
    have h := Nat.pow_le_pow_right (show 0<n+m+2 by omega) (show 1≤3 by omega)
    simp only [pow_one] at h
    omega
  calc
    _ ≤ 1200*(n+m+2)^3+50*(n+m+2)^3 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ h₁) (Nat.mul_le_mul_left _ h₂)
    _ = _ := by ring

/-- Counts the arithmetic evaluation, tape allocation, draws, and address
work for a scalar call. The extra address factor covers all tree accesses. -/
def calibrationFullQueryBound (n m R C : ℕ) : ℕ :=
  100*calibrationBankCallBound n m R C+450*(R+1)^4+15*C*16^R+
    5*C*16^R*(3*n+2)+2*C+(n+1)^2+20

lemma calibrationFullQueryBound_poly (n m R C : ℕ) :
    calibrationFullQueryBound n m R C≤100000000*(n+m+2)^3*(C+1)^2*16^R := by
  let N := n+m+2
  let q := (16 : ℕ)^R
  let D := N^3*(C+1)^2*q
  have hN : 1≤N := by dsimp [N]; omega
  have hC : 1≤(C+1)^2 := Nat.succ_le_of_lt (by positivity)
  have hq : 1≤q := Nat.succ_le_of_lt (by dsimp [q]; positivity)
  have hN3 : 1≤N^3 := by exact Nat.one_le_pow _ _ (by omega)
  have hNN : N≤N^3 := by simpa using Nat.pow_le_pow_right (show 0<N by omega) (show 1≤3 by omega)
  have hN2 : N*N≤N^3 := by
    have h : N^2≤N^3 := Nat.pow_le_pow_right (show 0<N by omega) (show 2≤3 by omega)
    simpa only [pow_two] using h
  have hBase : N^3≤D := by
    dsimp only [D]
    exact (Nat.le_mul_of_pos_right _ (by positivity : 0<(C+1)^2)).trans
      (Nat.le_mul_of_pos_right _ (by positivity : 0<q))
  have hProd : (n+1)*(m+1)≤D := by
    have h := Nat.mul_le_mul (show n+1≤N by dsimp [N]; omega) (show m+1≤N by dsimp [N]; omega)
    exact h.trans (hN2.trans hBase)
  have hSizeSq : (n+1)^2≤D :=
    (Nat.pow_le_pow_left (show n+1≤N by dsimp [N]; omega) 2).trans
      (by rw [pow_two]; exact hN2.trans hBase)
  have hSize : n+1≤D := by
    apply (show n+1≤N by dsimp [N]; omega).trans
    exact hNN.trans hBase
  have hCopy : C≤(C+1)^2 := by
    have h := Nat.pow_le_pow_right (Nat.succ_pos C) (show 1≤2 by omega)
    exact (Nat.le_succ C).trans (by simpa only [pow_one] using h)
  have hCopiesSquare : (C+1)^2≤D := by
    dsimp only [D]
    exact (Nat.le_mul_of_pos_left _ (by positivity : 0<N^3)).trans
      (Nat.le_mul_of_pos_right _ (by positivity : 0<q))
  have hCopyD := hCopy.trans hCopiesSquare
  have hR : R≤q := by
    exact (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left (by decide) _)
  have hqD : q≤D := by
    dsimp [D]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hRC : C*q≤D := by
    dsimp [D]
    exact Nat.mul_le_mul_right q (hCopy.trans (Nat.le_mul_of_pos_left _ (by positivity)))
  have hNode : C*(400*scalarPlannerPrimitiveBound n m*q)≤500000*D := by
    calc
      _ ≤ C*(400*(1250*N^3)*q) :=
        Nat.mul_le_mul_left C (Nat.mul_le_mul_right q (Nat.mul_le_mul_left 400
          (scalarPlannerPrimitiveBound_poly n m)))
      _ = 500000*(N^3*C*q) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right q (Nat.mul_le_mul_left _ hCopy))
  have hDraw : C*q*(3*n+2)≤3*D := by
    have h : 3*n+2≤3*N^3 := by dsimp [N] at hNN ⊢; omega
    calc
      _ ≤ C*q*(3*N^3) := Nat.mul_le_mul_left _ h
      _ = 3*(N^3*C*q) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right q (Nat.mul_le_mul_left _ hCopy))
  have hOne : 1≤D := hq.trans hqD
  have hAlloc := (levelAllocator_poly R).trans (show (16 : ℕ)^R≤D from hqD)
  have hRd := hR.trans hqD
  have he : 100000000*(n+m+2)^3*(C+1)^2*16^R=100000000*D := by
    dsimp only [D,N,q]
    ac_rfl
  rw [he]
  unfold calibrationFullQueryBound calibrationBankCallBound
  change 100*(46*(n+1)*(m+1)+80*(n+1)+
    C*(400*scalarPlannerPrimitiveBound n m*q+3)+10*(C+1)^2+3*R+31)+
      450*(R+1)^4+15*C*q+5*C*q*(3*n+2)+2*C+(n+1)^2+20 ≤ _
  rw [Nat.mul_add]
  have hh : 46*(n+1)*(m+1)=46*((n+1)*(m+1)) := by ring
  rw [hh, Nat.mul_add C, show 5*C*q*(3*n+2)=5*(C*q*(3*n+2)) by ring,
    show 15*C*q=15*(C*q) by ring]
  omega

/-- A single polynomial envelope for a public query scale. The exponent
is loose; it applies to both target and threshold calls. -/
theorem calibrationFullQueryBound_uniform {n m C : ℕ} [NeZero m] {h A : ℝ}
    (hh : h∈Ioo (0 : ℝ) 1) (hA : 0≤A) (hInv : h⁻¹≤A*((m : ℝ)+1)^3)
    (hC : C+1≤12*(n+m+2)^4) :
    (calibrationFullQueryBound n m (calibrationPlannerLevel m h) C : ℝ)≤
      (100000000*12^2*(6400 : ℝ)^4*((4 : ℝ)^8*2^32*A)^8)*((n : ℝ)+m+2)^291 := by
  let N := (n : ℝ)+m+2
  let B := (6400 : ℝ)^4*((4 : ℝ)^8*2^32*A)^8
  have hNR : (m : ℝ)+1≤N := by dsimp [N]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hP := calibrationLevel_poly hh hA hInv
  have hP' : (16 : ℝ)^calibrationPlannerLevel m h≤B*N^280 :=
    hP.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hNR _) (by positivity))
  have hC' : (C : ℝ)+1≤12*N^4 := by dsimp [N]; exact_mod_cast hC
  have hCs : ((C : ℝ)+1)^2≤(12*N^4)^2 := pow_le_pow_left₀ (by positivity) hC' _
  calc
    _ ≤ 100000000*N^3*((C : ℝ)+1)^2*(16 : ℝ)^calibrationPlannerLevel m h := by
      dsimp [N]
      exact_mod_cast calibrationFullQueryBound_poly n m (calibrationPlannerLevel m h) C
    _ ≤ 100000000*N^3*(12*N^4)^2*(B*N^280) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hCs (by positivity)) hP' (by positivity) (by positivity)
    _ = (100000000*12^2*B)*N^291 := by
      rw [mul_pow,← pow_mul,show (4 : ℕ)*2=8 by decide,
        show (291 : ℕ)=3+8+280 by decide,pow_add,pow_add]
      ac_rfl
    _ = _ := by dsimp [B,N]; ac_rfl

open ProphetSecretary.Probability

lemma targetCopies_poly (n m : ℕ) (hm : 0<m)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j≤1/((m : ℝ)^2*(4*(m : ℝ)+1))) :
    confidenceCopyCount _ H+1≤12*(n+m+2)^4 := by
  let N := n+m+2
  have hN : 0<N := by dsimp [N]; omega
  have hNm : m≤N := by dsimp [N]; omega
  have ha : m^2*(4*m+1)≤5*N^3 := by
    calc
      _ ≤ N^2*(5*N) := Nat.mul_le_mul (Nat.pow_le_pow_left hNm _) (by omega)
      _ = _ := by ring
  have hb : N^3≤N^4 := Nat.pow_le_pow_right hN (by omega)
  have hc : 1≤N^4 := Nat.one_le_pow _ _ hN
  have hd := targetConfidenceCount_le m H hm
  change _ ≤ 12*N^4
  omega

lemma thresholdCopies_poly (n m J : ℕ) (hn : 0<n) (hm : 0<m) (hJ : J≤m)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j≤policyFailureBound n m J) :
    confidenceCopyCount _ H+1≤12*(n+m+2)^4 := by
  let N := n+m+2
  have hN : 0<N := by dsimp [N]; omega
  have ha : m^2*n*(J+1)≤N^4 := by
    calc
      _ ≤ N^2*N*N := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left
        (show m≤N by dsimp [N]; omega) _) (show n≤N by dsimp [N]; omega)) (by dsimp [N]; omega)
      _ = _ := by ring
  have hb : 1≤N^4 := Nat.one_le_pow _ _ hN
  have hd := policyConfidenceCount_le n m J H hn hm
  change _ ≤ 12*N^4
  omega

noncomputable def calibrationWorkConstant (zlo : ℝ) : ℝ :=
  100000000*12^2*(6400 : ℝ)^4*((4 : ℝ)^8*2^32*(1+196/zlo))^8

theorem calibrationTargetQueryWork_polynomial {n m : ℕ} [NeZero m] (hm : 2≤m)
    {zlo : ℝ} (hz : 0<zlo)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j≤1/((m : ℝ)^2*(4*(m : ℝ)+1))) :
    let h := 1/(m : ℝ)
    (calibrationFullQueryBound n m (calibrationPlannerLevel m h)
      (confidenceCopyCount _ H) : ℝ) ≤ calibrationWorkConstant zlo*((n : ℝ)+m+2)^291 := by
  dsimp only
  apply calibrationFullQueryBound_uniform (targetAccuracy_mem hm)
    (by positivity : 0≤1+196/zlo) ?_
    (targetCopies_poly n m (NeZero.pos m) H)
  rw [targetAccuracy_inv]
  have hp : (m : ℝ)+1≤((m : ℝ)+1)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) m] :
      (1 : ℝ)≤(m : ℝ)+1) (by omega : 1≤3)
  exact (by linarith : (m : ℝ)≤(m : ℝ)+1).trans (hp.trans
    (le_mul_of_one_le_left (by positivity) (by linarith [div_nonneg (by norm_num : (0 : ℝ)≤196) hz.le])))

theorem calibrationThresholdQueryWork_polynomial {n m J : ℕ} [NeZero m]
    (hn : 0<n) (hm : 2≤m) (hJ : J≤m) {zlo : ℝ} (hz : zlo∈Ioo (0 : ℝ) (1/4))
    (H : ∃ j : ℕ, (1/4 : ℝ)^j≤policyFailureBound n m J) :
    let h := policyAccuracy m zlo
    (calibrationFullQueryBound n m (calibrationPlannerLevel m h)
      (confidenceCopyCount _ H) : ℝ) ≤ calibrationWorkConstant zlo*((n : ℝ)+m+2)^291 := by
  dsimp only
  apply calibrationFullQueryBound_uniform (policyAccuracy_mem hm hz)
    (by have := hz.1; positivity : 0≤1+196/zlo) ?_
    (thresholdCopies_poly n m J hn (NeZero.pos m) hJ H)
  have h : (49 : ℝ)/zlo≤1+196/zlo :=
    (div_le_div_of_nonneg_right (by norm_num : (49 : ℝ)≤196) hz.1.le).trans
      (le_add_of_nonneg_left zero_le_one)
  exact (policyAccuracy_inv_le (m := m) hz.1).trans (mul_le_mul_of_nonneg_right h (by positivity))

end ProphetSecretary.Statistics.Calibration
