import ProphetSecretary.Analysis.PolynomialWorkBound
import ProphetSecretary.Statistics.FinitePublicScales

/-!
# Polynomial bounds for the finite calibration schedule

The coefficient and its public inverse bound are fixed before the
instance size. The bounds combine the actual schedule parameters,
rather than allowing a separate constant for each instance.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

private structure FiniteScheduleInput (zlo : ℚ) (zInv : ℕ) where
  n : ℕ
  m : ℕ
  param : FairCalibrationParameters n m
  coefficient_eq : (zlo : ℝ)=param.zlo
  inverse_eq : param.clockInverse=zInv

private def finiteScheduleSize {zlo : ℚ} {zInv : ℕ} (x : FiniteScheduleInput zlo zInv) : ℕ :=
  x.n+x.m+2

private theorem finiteScheduleSize_pos {zlo : ℚ} {zInv : ℕ} (x : FiniteScheduleInput zlo zInv) :
    0<finiteScheduleSize x := by simp [finiteScheduleSize]

private noncomputable def scheduleOf {zlo : ℚ} {zInv : ℕ} (target : Bool)
    (x : FiniteScheduleInput zlo zInv) : FairCallSchedule :=
  if target then x.param.nativeTargetSchedule else x.param.nativeThresholdSchedule zlo x.coefficient_eq

private theorem schedule_level_polynomial (zlo : ℚ) (zInv : ℕ) (target : Bool) :
    HasPolynomialWorkBound (finiteScheduleSize (zlo:=zlo) (zInv:=zInv))
      (fun x => (16:ℕ)^(scheduleOf target x).level) := by
  apply HasPolynomialWorkBound.of_real_bound (finiteLevelConstant (zlo:ℝ)) 280
  intro x
  have h : (16:ℝ)^(scheduleOf target x).level≤
      finiteLevelConstant x.param.zlo*((x.m:ℝ)+1)^280 := by
    cases target
    · exact finiteThresholdLevel_bound x.param zlo x.coefficient_eq
    · exact finiteTargetLevel_bound x.param
  have hm : (x.m:ℝ)+1≤(finiteScheduleSize x:ℝ) := by
    exact_mod_cast (show x.m+1≤finiteScheduleSize x by unfold finiteScheduleSize; omega)
  rw [Nat.cast_pow,Nat.cast_ofNat]
  rw [←x.coefficient_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm _)
    (by unfold finiteLevelConstant; positivity))

private theorem schedule_bits_polynomial (zlo : ℚ) (zInv : ℕ) (target : Bool) :
    HasPolynomialWorkBound (finiteScheduleSize (zlo:=zlo) (zInv:=zInv))
      (fun x => (scheduleOf target x).bits) := by
  apply HasPolynomialWorkBound.of_real_bound (finiteQueryBitConstant (zlo:ℝ)) 36
  intro x
  have h : ((scheduleOf target x).bits:ℝ)≤finiteQueryBitConstant x.param.zlo*((x.n:ℝ)+x.m+2)^36 := by
    cases target
    · exact finiteThresholdBits_bound x.param zlo x.coefficient_eq
    · exact finiteTargetBits_bound x.param
  simpa only [finiteScheduleSize,Nat.cast_add,Nat.cast_ofNat,←x.coefficient_eq] using h

private theorem schedule_copies_polynomial (zlo : ℚ) (zInv : ℕ) (target : Bool) :
    HasPolynomialWorkBound (finiteScheduleSize (zlo:=zlo) (zInv:=zInv))
      (fun x => confidenceCopyCount (scheduleOf target x).failure (scheduleOf target x).confidence) := by
  refine ⟨12,4,fun x => ?_⟩
  have h : confidenceCopyCount (scheduleOf target x).failure (scheduleOf target x).confidence+1≤
      12*finiteScheduleSize x^4 := by
    cases target
    · exact finiteThresholdCopies_bound x.param zlo x.coefficient_eq
    · exact finiteTargetCopies_bound x.param
  exact (Nat.le_succ _).trans h

private theorem schedule_grid_le (zlo : ℚ) (zInv : ℕ) (x : FiniteScheduleInput zlo zInv) :
    x.param.grid≤x.m :=
  familyGridSize_le (by linarith only [x.param.coefficient_mem.1])

private lemma pilotRounds_polynomial (zlo : ℚ) (zInv : ℕ) :
    HasPolynomialWorkBound (finiteScheduleSize (zlo:=zlo) (zInv:=zInv))
      (fun x => outerPilotRounds x.m) := by
  refine ⟨12000,1,fun x => ?_⟩
  have hm := clog_two_le_self (2*x.m)
  unfold outerPilotRounds outerPilotRank finiteScheduleSize
  simp only [pow_one]
  omega

private lemma scheduleWork_add {zlo : ℚ} {zInv : ℕ} {F G : FiniteScheduleInput zlo zInv → ℕ}
    (hF : HasPolynomialWorkBound finiteScheduleSize F) (hG : HasPolynomialWorkBound finiteScheduleSize G) :
    HasPolynomialWorkBound finiteScheduleSize (fun x => F x+G x) :=
  HasPolynomialWorkBound.add finiteScheduleSize_pos hF hG

local infixl:65 " +ₚ " => scheduleWork_add
local infixl:70 " *ₚ " => HasPolynomialWorkBound.mul
local infixr:80 " ^ₚ " => HasPolynomialWorkBound.pow

private theorem schedule_work_polynomial (zlo : ℚ) (zInv : ℕ) (target : Bool) :
    HasPolynomialWorkBound (finiteScheduleSize (zlo:=zlo) (zInv:=zInv))
      (fun x => (scheduleOf target x).work x.n x.m) := by
  let N := finiteScheduleSize (zlo:=zlo) (zInv:=zInv)
  have hn : HasPolynomialWorkBound N (fun x => x.n) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N finiteScheduleSize; omega)
  have hm : HasPolynomialWorkBound N (fun x => x.m) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N finiteScheduleSize; omega)
  have hExp := schedule_level_polynomial zlo zInv target
  have hB := schedule_bits_polynomial zlo zInv target
  have hC := schedule_copies_polynomial zlo zInv target
  have hR : HasPolynomialWorkBound N (fun x => (scheduleOf target x).level) := hExp.of_le (fun x =>
    (Nat.lt_two_pow_self (n := (scheduleOf target x).level)).le.trans
      (Nat.pow_le_pow_left (by decide : 2≤16) _))
  let c := HasPolynomialWorkBound.const N
  have hn1 := hn +ₚ c 1
  have hm1 := hm +ₚ c 1
  have hPrimitive : HasPolynomialWorkBound N (fun x => scalarPlannerPrimitiveBound x.n x.m) :=
    c 1200 *ₚ hn1 ^ₚ 3 +ₚ c 50 *ₚ (hn +ₚ hm +ₚ c 1)
  have hDecode : HasPolynomialWorkBound N (fun x => plannerFairDecodeBound x.n (scheduleOf target x).bits) :=
    (c 3 *ₚ hn +ₚ c 2) *ₚ (c 8 *ₚ hB +ₚ c 4) +ₚ c 2 *ₚ hB +ₚ c 1 +ₚ c 15 *ₚ hn1
  exact c 46 *ₚ hn1 *ₚ hm1 +ₚ c 80 *ₚ hn1 +ₚ
    hC *ₚ (c 400 *ₚ hPrimitive *ₚ hExp +ₚ c 3) +ₚ c 10 *ₚ (hC +ₚ c 1) ^ₚ 2 +ₚ
    c 4 *ₚ hC *ₚ hExp *ₚ (hDecode +ₚ c 40) +ₚ c 11 *ₚ hR +ₚ c 4 *ₚ hC +ₚ c 100

private noncomputable def scheduleFairBitEnvelope {zlo : ℚ} {zInv : ℕ}
    (x : FiniteScheduleInput zlo zInv) : ℕ :=
  finiteScheduleFairBitsBound x.n x.m x.param.grid x.param.clockBits x.param.coinBits
    (outerMarkBits x.n x.m) (scheduleOf true x) (scheduleOf false x)

private noncomputable def scheduleArithmeticEnvelope {zlo : ℚ} {zInv : ℕ}
    (x : FiniteScheduleInput zlo zInv) : ℕ :=
  finiteScheduleArithmeticBound x.n x.m x.param.grid x.param.clockBits x.param.coinBits
    (outerMarkBits x.n x.m) (scheduleOf true x) (scheduleOf false x)

private theorem schedule_envelopes_polynomial (zlo : ℚ) (zInv : ℕ) :
    HasPolynomialWorkBound (finiteScheduleSize (zlo:=zlo) (zInv:=zInv))
      (fun x => scheduleFairBitEnvelope x+scheduleArithmeticEnvelope x) := by
  let N := finiteScheduleSize (zlo:=zlo) (zInv:=zInv)
  have hn : HasPolynomialWorkBound N (fun x => x.n) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N finiteScheduleSize; omega)
  have hm : HasPolynomialWorkBound N (fun x => x.m) :=
    (HasPolynomialWorkBound.size N).of_le (fun x => by unfold N finiteScheduleSize; omega)
  have hJ : HasPolynomialWorkBound N (fun x => x.param.grid) :=
    hm.of_le (schedule_grid_le zlo zInv)
  have hb : HasPolynomialWorkBound N (fun x => x.param.clockBits) := by
    refine ⟨400*(zInv+1),5,fun x => ?_⟩
    simpa only [N,finiteScheduleSize,x.inverse_eq] using finiteClockBits_polynomial x.param
  have hc : HasPolynomialWorkBound N (fun x => x.param.coinBits) :=
    ⟨1,2,fun x => by simpa only [N,finiteScheduleSize,Nat.one_mul] using finiteCoinBits_bound x.param⟩
  have ho : HasPolynomialWorkBound N (fun x => outerMarkBits x.n x.m) :=
    ⟨12004^2,6,fun x => finiteOuterMarkBits_bound x.n x.m⟩
  have hSlots : HasPolynomialWorkBound N (fun x => outerMarkSlotCount x.n x.m) :=
    ⟨12004,2,fun x => finiteOuterMarkSlots_bound x.n x.m⟩
  have hPilot := pilotRounds_polynomial zlo zInv
  have hET := schedule_level_polynomial zlo zInv true
  have hEP := schedule_level_polynomial zlo zInv false
  have hBT := schedule_bits_polynomial zlo zInv true
  have hBP := schedule_bits_polynomial zlo zInv false
  have hCT := schedule_copies_polynomial zlo zInv true
  have hCP := schedule_copies_polynomial zlo zInv false
  have hWT := schedule_work_polynomial zlo zInv true
  have hWP := schedule_work_polynomial zlo zInv false
  have hRT : HasPolynomialWorkBound N (fun x => ((scheduleOf true x).level+1)^4) :=
    hET.of_le (fun x => levelAllocator_poly _)
  have hRP : HasPolynomialWorkBound N (fun x => ((scheduleOf false x).level+1)^4) :=
    hEP.of_le (fun x => levelAllocator_poly _)
  let c := HasPolynomialWorkBound.const N
  have hn1 := hn +ₚ c 1
  have hm1 := hm +ₚ c 1
  have hJ1 := hJ +ₚ c 1
  have hTargetSlots := c 4 *ₚ hm +ₚ c 1
  have hCoordinates := c 3 *ₚ hn +ₚ c 2
  have hPolicySlots := hm1 *ₚ hn *ₚ hJ1
  have hFair : HasPolynomialWorkBound N scheduleFairBitEnvelope :=
    hTargetSlots *ₚ (c 5 *ₚ hCT *ₚ hET *ₚ (hCoordinates *ₚ hBT)) +ₚ
    hPolicySlots *ₚ (c 5 *ₚ hCP *ₚ hEP *ₚ (hCoordinates *ₚ hBP)) +ₚ
    hSlots *ₚ ho +ₚ hn *ₚ (c 2 *ₚ hm +ₚ c 1) *ₚ hb +ₚ hc
  have hStorageT := c 540 *ₚ hRT +ₚ hCT *ₚ hET *ₚ
    (c 15 +ₚ c 5 *ₚ (hCoordinates *ₚ (c 5 *ₚ hBT +ₚ c 10) +ₚ c 30))
  have hStorageP := c 540 *ₚ hRP +ₚ hCP *ₚ hEP *ₚ
    (c 15 +ₚ c 5 *ₚ (hCoordinates *ₚ (c 5 *ₚ hBP +ₚ c 10) +ₚ c 30))
  have hStorage := hTargetSlots *ₚ hStorageT +ₚ hPolicySlots *ₚ hStorageP +ₚ
    c 10 *ₚ (hTargetSlots +ₚ hm1 *ₚ (hn *ₚ hJ1) +ₚ hm +ₚ c 1) +ₚ c 6
  have hTarget := hWT +ₚ hn +ₚ c 3
  have hPolicy := hWP +ₚ c 1 +ₚ c 3 *ₚ hn +ₚ c 10 *ₚ hn1 ^ₚ 2
  have hGridClock := hn *ₚ (c 8 *ₚ hb +ₚ c 11) +ₚ c 3
  have hOrder := hGridClock +ₚ c 28 *ₚ hn1 ^ₚ 2
  have hClock := hGridClock +ₚ c 20 *ₚ hn1 ^ₚ 2 +ₚ c 2 *ₚ hb +ₚ c 1
  have hDecode := hm *ₚ (hOrder +ₚ hClock +ₚ c 4) +ₚ hClock +ₚ
    c 10 *ₚ hc +ₚ c 7 +ₚ c 8 *ₚ hm1 +ₚ c 8
  have hPrep := hDecode +ₚ c 100 *ₚ hn1 ^ₚ 2 *ₚ hm1 ^ₚ 2 +ₚ c 26 *ₚ hn1 *ₚ hm1 +ₚ
    hTargetSlots *ₚ (hTarget +ₚ c 10) +ₚ c 8 +ₚ
    hm *ₚ (hn *ₚ (hn *ₚ (hm +ₚ c 2) +ₚ c 7 +ₚ hJ1 *ₚ (hPolicy +ₚ c 2)) +ₚ
      hJ1 *ₚ (c 12 *ₚ hn +ₚ c 3) +ₚ c 6) +ₚ
    c 10 *ₚ hm1 *ₚ (hJ +ₚ c 3) +ₚ c 8 *ₚ hJ1 +ₚ c 4 *ₚ (hJ +ₚ c 2) +ₚ c 2 *ₚ hc +ₚ c 42
  have hOuter := hSlots *ₚ (c 10 *ₚ ho +ₚ c 15) +ₚ c 5 +ₚ
    (c 10 *ₚ hm1 *ₚ hn1 +ₚ c 20 *ₚ (hPilot +ₚ c 1) ^ₚ 2 *ₚ hn1 +ₚ c 5 +ₚ
      hn *ₚ (c 2 *ₚ hm) *ₚ (c 4 *ₚ hm +ₚ c 21)) +ₚ hPrep +ₚ c 4
  have hDecision := hn *ₚ (hm +ₚ c 4) +ₚ c 18 +ₚ c 4 *ₚ hn +ₚ hJ1 *ₚ (hPolicy +ₚ c 2)
  have hArithmetic : HasPolynomialWorkBound N scheduleArithmeticEnvelope :=
    hStorage +ₚ hOuter +ₚ hn *ₚ (hDecision +ₚ hn1 *ₚ (c 4 *ₚ hm +ₚ c 24) +ₚ c 9)
  exact hFair +ₚ hArithmetic

/-- One coefficient and exponent bound the arithmetic work and the fair
bits of the actual public schedule at a fixed coefficient and inverse. -/
theorem finiteScheduleBounds_polynomial (zlo : ℚ) (zInv : ℕ) :
    ∃ C d : ℕ, ∀ {n m : ℕ} (a : FairCalibrationParameters n m)
      (hz : (zlo:ℝ)=a.zlo) (_ : a.clockInverse=zInv),
      finiteScheduleFairBitsBound n m a.grid a.clockBits a.coinBits (outerMarkBits n m)
        a.nativeTargetSchedule (a.nativeThresholdSchedule zlo hz)≤C*(n+m+2)^d ∧
      finiteScheduleArithmeticBound n m a.grid a.clockBits a.coinBits (outerMarkBits n m)
        a.nativeTargetSchedule (a.nativeThresholdSchedule zlo hz)≤C*(n+m+2)^d := by
  obtain ⟨C,d,h⟩ := schedule_envelopes_polynomial zlo zInv
  refine ⟨C,d,fun {n m} a hz hi => ?_⟩
  let x : FiniteScheduleInput zlo zInv := ⟨n,m,a,hz,hi⟩
  have hw := h x
  exact ⟨(Nat.le_add_right _ _).trans hw,(Nat.le_add_left _ _).trans hw⟩

end ProphetSecretary.Statistics.Calibration
