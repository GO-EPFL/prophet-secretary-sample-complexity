import ProphetSecretary.Statistics.CalibratedOuter.BinaryExecutablePolynomial
import ProphetSecretary.Statistics.CalibratedOuter.BinaryTape

/-!
# The binary learner's hard budgets

The measured preparation uses exactly the rows returned by the sample
requests. Each online decision receives its current offer and prefix
history. The sum may include all arrivals, so stopping early preserves
the work bound.
-/

open Set
open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Model

private lemma countedVectorRequests {A : Type} {n : ℕ} (sample : Fin n → StateM ℕ A)
    (counters : Fin n → ℕ) (h : ∀ i c, ((sample i).run c).2=c+counters i) (s : ℕ) :
    ((Vector.ofFnM sample).run s).2=s+∑ i, counters i := by
  induction n with
  | zero =>
    rw [Vector.ofFnM_zero]
    change s=s+∑ i, counters i
    simp
  | succ n ih =>
    rw [Vector.ofFnM_succ]
    change ((sample (Fin.last n)).run
      ((Vector.ofFnM (fun i : Fin n => sample i.castSucc)).run s).2).2 = _
    rw [h,ih _ _ (fun i c => h i.castSucc c),Fin.sum_univ_castSucc,Nat.add_assoc]

/-- Counting only requests to one distribution gives exactly the stored row
length for every execution. -/
theorem countedFullSamplesM_marginalCounter {A : Type} (n m : ℕ) (j : Fin n)
    (sample : Fin n → StateM ℕ A)
    (h : ∀ i c, ((sample i).run c).2=c+(if i=j then 1 else 0)) (s : ℕ) :
    ((countedFullSamplesM n m sample).run s).2=s+m := by
  unfold countedFullSamplesM
  change ((Vector.ofFnM (fun i : Fin n => Vector.ofFnM (fun _ : Fin m => sample i))).run s).2 = _
  rw [countedVectorRequests _ (fun i => m*(if i=j then 1 else 0)) (fun i c =>
    uniformVectorM_counter (sample i) _ (h i) m c)]
  congr 1
  simp [mul_ite]

namespace BinaryScheduleInput

variable {zlo : ℚ} {zInv : ℕ}

noncomputable def measuredProgramWork (x : BinaryScheduleInput zlo zInv)
    (mu z : BinaryRational) (ez : z.value=zlo) (t : x.parameters.NativeOuterTape x.coefficient_eq)
    (sample : Fin x.n → StateM ℕ BinaryRational) (s : ℕ)
    (S : Finset (Fin x.n)) (k : Fin x.n → Fin x.n) (offer : Fin x.n → BinaryRational)
    (hist : Fin x.n → BinaryOuterHistory x.n (Fin x.n)) : ℕ :=
  let input := (countedFullSamplesM x.n (outerSampleBudget x.m) sample).run s
  let hZ : (z.value : ℝ)=x.parameters.zlo := congrArg (fun q : ℚ => (q : ℝ)) ez |>.trans x.coefficient_eq
  let tape : x.parameters.NativeOuterTape hZ := by subst zlo; exact t
  let p := x.parameters.prepareBinaryTapeProgram mu z hZ input.1.1 tape
  input.1.2+x.parameters.nativeOuterTapeBitCount x.coefficient_eq+p.1.work+p.2+
    (∑ i ∈ S, (x.parameters.decideBinaryProgram p.1 (k i) i (offer i) (hist i)).2)

/-- Hard resource bounds for every training and online outcome of the
binary program. -/
def HasHardBounds (x : BinaryScheduleInput zlo zInv) (D C e : ℕ) : Prop :=
    ∀ (mu z : BinaryRational) (ez : z.value=zlo),
      RationalHeight mu.value D → RationalHeight z.value D → 2≤D →
      ∀ (t : x.parameters.NativeOuterTape x.coefficient_eq)
        (sample : Fin x.n → StateM ℕ BinaryRational) (s : ℕ),
      (∀ i c, ((sample i).run c).2=c+1) →
      ∀ (S : Finset (Fin x.n)) (k : Fin x.n → Fin x.n) (offer : Fin x.n → BinaryRational)
        (hist : Fin x.n → BinaryOuterHistory x.n (Fin x.n)),
      (∀ i j, RationalHeight
        (((countedFullSamplesM x.n (outerSampleBudget x.m) sample).run s).1.1 i j).value x.width) →
      (∀ i, RationalHeight (offer i).value x.width) →
      (∀ i j t v, hist i j=some (t,v) → RationalHeight v.value x.width) →
      ((countedFullSamplesM x.n (outerSampleBudget x.m) sample).run s).2 =
        s+x.n*outerSampleBudget x.m ∧
      x.parameters.nativeOuterTapeBitCount x.coefficient_eq ≤ C*x.size^e ∧
      x.measuredProgramWork mu z ez t sample s S k offer hist ≤ C*x.size^e

/-- One polynomial bounds both binary work and the number of primitive
fair bits in the tape used in the reward law. -/
theorem measuredProgramWork_polynomial (D : ℕ) :
    ∃ C e : ℕ, ∀ x : BinaryScheduleInput zlo zInv, x.HasHardBounds D C e := by
  obtain ⟨C,e,hP⟩ := executableBinaryWorkBudget_polynomial (zlo := zlo) (zInv := zInv) D
  refine ⟨C,e,?_⟩
  intro x mu z ez hmu hz hD tape sample s hSample S k offer hist hY ho hHist
  subst zlo
  let a := x.parameters
  let hZ := x.coefficient_eq
  let y := ((countedFullSamplesM x.n (outerSampleBudget x.m) sample).run s).1.1
  let p := a.prepareBinaryTapeProgram mu z hZ y tape
  let B := x.outerWidth
  let seed := (a.countedNativeOuterTape hZ tape).1
  let q := a.prepareBinaryProgram mu z hZ y seed
  have hEq : p.1=q := a.prepareBinaryTapeProgram_value mu z hZ y tape
  have hY' (i j) : RationalHeight (y i j).value B := (hY i j).mono (by unfold B outerWidth; omega)
  have hMarks : outerMarkBits x.n x.m≤B := by unfold B outerWidth; omega
  have hPrep := a.prepareBinaryProgram_work mu z hZ y seed D B hY' hMarks hmu hz hD
  change q.work≤x.publicStartupBudget D+
    binaryOuterStageWorkBound x.n x.m (outerMarkBits x.n x.m) x.m B (x.boundedPrepareBudget D)+3 at hPrep
  have hO (i : Fin x.n) : (a.decideBinaryProgram q (k i) i (offer i) (hist i)).2 ≤
      x.boundedOnlineBudget D+binaryOuterOnlineOverhead x.n x.m x.m B :=
    a.decideBinaryProgram_work mu z hZ y seed D B hY' hMarks hz hD (k i) i (offer i) (hist i)
      ((ho i).mono (by unfold B outerWidth; omega))
      (fun j t v hv => (hHist i j t v hv).mono (by unfold B outerWidth; omega))
  have hS : (∑ i∈S, (a.decideBinaryProgram q (k i) i (offer i) (hist i)).2)≤
      x.n*(x.boundedOnlineBudget D+binaryOuterOnlineOverhead x.n x.m x.m B) := by
    calc
      _ ≤ ∑ _i∈S, (x.boundedOnlineBudget D+binaryOuterOnlineOverhead x.n x.m x.m B) :=
        Finset.sum_le_sum (fun i _ => hO i)
      _ = _ := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (S.card_le_univ.trans_eq (Fintype.card_fin x.n))
  have hExtra := a.prepareBinaryTapeProgram_extra_work mu z hZ y tape D hz
  change p.2≤finiteQueryStorageBound x.n x.m a.grid a.nativeTargetSchedule
    (a.nativeThresholdSchedule z.value hZ)+FairCalibrationParameters.executablePublicSetupExtraBound x.n x.m a.grid D+
      binaryPublicIntegersWork x.n x.m a.clockInverse at hExtra
  have hExtra' : p.2≤x.allocationBudget+x.executableSetupBudget D := by
    rw [show a.clockInverse=zInv from x.inverse_eq] at hExtra
    unfold allocationBudget finiteScheduleArithmeticBound executableSetupBudget
    dsimp only [a,hZ] at hExtra
    omega
  have hBits : a.nativeOuterTapeBitCount hZ≤x.bitBudget := a.nativeOuterTapeBitCount_le hZ
  have hCD : 3≤x.clockDecodeBudget := by unfold clockDecodeBudget; omega
  have hW : x.measuredProgramWork mu z rfl tape sample s S k offer hist ≤
      x.workBudget (x.boundedPrepareBudget D) (x.boundedOnlineBudget D) (2*x.publicStartupBudget D)+
        2*x.executableSetupBudget D := by
    unfold measuredProgramWork
    dsimp only
    rw [countedFullSamplesM_work]
    change 8*(x.n+1)*(outerSampleBudget x.m+1)+a.nativeOuterTapeBitCount hZ+p.1.work+p.2+
      (∑ i∈S,(a.decideBinaryProgram p.1 (k i) i (offer i) (hist i)).2)≤_
    rw [hEq]
    unfold workBudget
    dsimp only [B] at hPrep hS
    omega
  refine ⟨countedFullSamplesM_counter _ _ sample hSample s,?_,hW.trans (hP x)⟩
  exact hBits.trans ((by unfold workBudget; omega : x.bitBudget≤x.workBudget
    (x.boundedPrepareBudget D) (x.boundedOnlineBudget D) (2*x.publicStartupBudget D)+
      2*x.executableSetupBudget D).trans (hP x))

end BinaryScheduleInput

private lemma rationalHeight_exists (q : ℚ) : ∃ D : ℕ, RationalHeight q D := by
  refine ⟨max q.num.natAbs q.den, ?_, ?_⟩
  exact (le_max_left _ _).trans (Nat.lt_two_pow_self (n := max q.num.natAbs q.den)).le
  exact (le_max_right _ _).trans (Nat.lt_two_pow_self (n := max q.num.natAbs q.den)).le

/-- The finite-bit learner uses the same endpoint for the statistical
guarantee and the uniform work bound. The width in the latter bounds the
rational inputs on the execution under consideration. -/
theorem binary_finite_bit_learner :
    ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (zInv : ℕ)
      (hInv : 1/((1-(b : ℝ))/(b : ℝ))≤(zInv : ℝ)) (A eps0 : ℝ) (D C e : ℕ),
      0<A ∧ 0<eps0 ∧
      RationalHeight (1/10000000 : ℚ) D ∧ RationalHeight ((1-b)/b) D ∧ 2≤D ∧
      (∀ x : BinaryScheduleInput ((1-b)/b) zInv, x.HasHardBounds D C e) ∧
      ∀ eps∈Ioo (0 : ℝ) eps0,
        ∃ (m : ℕ) (hm : 2≤m), (outerSampleBudget m : ℝ)≤A/eps ∧
          ∀ (n : ℕ) (hn : 0<n) (P : RationalOfferInstance n), P.toInstance.HasPositiveFiniteMaximum →
            let a : FairCalibrationParameters n m :=
              ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
            let zlo := BinaryRational.ofRat ((1-b)/b)
            let hz : (zlo.value : ℝ)=a.zlo := by
              simp only [zlo,BinaryRational.ofRat_value,Rat.cast_div,Rat.cast_sub,Rat.cast_one]
              rfl
            (optimalCompetitiveRatio-eps)*P.toInstance.expectedMaximum ≤
              a.binaryTapeExpectedReward (BinaryRational.ofRat (1/10000000)) zlo hz P := by
  obtain ⟨b,hb,zInv,hInv,A,eps0,hA,heps,hReward⟩ := binary_finite_bit_sample_upper_bound
  obtain ⟨D₁,h₁⟩ := rationalHeight_exists (1/10000000)
  obtain ⟨D₂,h₂⟩ := rationalHeight_exists ((1-b)/b)
  let D := max 2 (max D₁ D₂)
  obtain ⟨C,e,hWork⟩ := BinaryScheduleInput.measuredProgramWork_polynomial
    (zlo := (1-b)/b) (zInv := zInv) D
  refine ⟨b,hb,zInv,hInv,A,eps0,D,C,e,hA,heps,
    h₁.mono ((le_max_left _ _).trans (le_max_right _ _)),
    h₂.mono ((le_max_right _ _).trans (le_max_right _ _)),
    le_max_left _ _,hWork,?_⟩
  intro eps he
  obtain ⟨m,hm,hB,hR⟩ := hReward eps he
  refine ⟨m,hm,hB,?_⟩
  intro n hn P hP
  dsimp only
  rw [FairCalibrationParameters.binaryTapeExpectedReward_eq]
  exact hR n hn P hP

end ProphetSecretary.Statistics.Calibration
