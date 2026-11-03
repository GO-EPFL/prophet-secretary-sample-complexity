import ProphetSecretary.Statistics.StandaloneBinaryPlannerWork

/-!
# Uniform size of the standalone binary schedule

The full tree factor is bounded by the empirical weight and inverse
accuracy. The copy count retains logarithmic dependence on the failure
probability. No positive-count cutoff is imposed.
-/

open Set MeasureTheory

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ} {k : Fin n → ℕ}

noncomputable def standaloneBinaryInputSize (n m B : ℕ) (h p : ℝ) : ℝ :=
  n+m+B+1/h+Real.log (1/p)+4

private lemma one_le_log_four : 1≤Real.log 4 := by
  have h := Real.log_le_log (Real.exp_pos 1)
    (Real.exp_one_lt_three.le.trans (show (3:ℝ)≤4 by norm_num))
  simpa only [Real.log_exp] using h

private lemma standaloneWeight_count [∀ i, NeZero (k i)]
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0≤y i j)
    (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup) :
    scalarPlannerWeight y (scalarPlannerListInterpret x).1≤
      Real.exp (4*(empiricalPlannerInstance y hy).positiveCount) := by
  rw [←storedScalarPlannerWeight_value y x hx]
  exact storedScalarPlannerWeight_le_exp_count y hy x hx

set_option maxHeartbeats 600000 in
theorem standaloneBinarySchedule_size [∀ i, NeZero (k i)]
    (y : (i : Fin n) → Fin (k i) → BinaryRational) (hy : ∀ i j, 0≤((y i j).value:ℝ))
    (x : ScalarPlannerListState n BinaryRational) (hx : x.1.Nodup) (h p : BinaryRational)
    (hh : (h.value:ℝ)∈Ioo (0:ℝ) 1) (hp : (p.value:ℝ)∈Ioo (0:ℝ) (1/2)) (m B : ℕ) :
    let L := (empiricalPlannerInstance (fun i j => ((y i j).value:ℝ)) hy).positiveCount
    let S := standaloneBinaryInputSize n m B (h.value:ℝ) (p.value:ℝ)
    let q := countedBinaryStandalonePlan (plannerStoredRows y) x h p
    ((n+m+B+q.precision+16^q.level+q.halfCopies+2 : ℕ):ℝ)≤
      ((6400:ℝ)^4*2^8+100)*(S*Real.exp (4*L))^16 := by
  dsimp only
  let yR := fun i j => ((y i j).value:ℝ)
  let xL := scalarPlannerStateRatCast (scalarPlannerStateValueMap BinaryRational.value x)
  let β := scalarPlannerWeight yR (scalarPlannerListInterpret xL).1
  let L := (empiricalPlannerInstance yR hy).positiveCount
  let E := Real.exp (4*L)
  let S := standaloneBinaryInputSize n m B (h.value:ℝ) (p.value:ℝ)
  let N := S*E
  let q := countedBinaryStandalonePlan (plannerStoredRows y) x h p
  let K := (6400:ℝ)^4*2^8
  have hβ : 1≤β := scalarPlannerWeight_ge_one _ _
  have hβE : β≤E := standaloneWeight_count yR hy xL hx
  have hE : 1≤E := hβ.trans hβE
  have hp1 : (p.value:ℝ)<1 := hp.2.trans (by norm_num)
  have hpLog : 0≤Real.log (1/(p.value:ℝ)) :=
    Real.log_nonneg ((one_le_div hp.1).mpr (by simpa only [one_mul] using hp1.le))
  have hInv0 : 0≤1/(h.value:ℝ) := div_nonneg zero_le_one hh.1.le
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg m
  have hB0 : (0:ℝ)≤B := Nat.cast_nonneg B
  have hS : 1≤S := by
    unfold S standaloneBinaryInputSize
    linarith only [hpLog,hInv0,hn0,hm0,hB0]
  have hSN : S≤N := le_mul_of_one_le_right (zero_le_one.trans hS) hE
  have hEN : E≤N := le_mul_of_one_le_left (zero_le_one.trans hE) hS
  have hN : 1≤N := hS.trans hSN
  have hInv : 1/(h.value:ℝ)≤N := (show 1/(h.value:ℝ)≤S by
    unfold S standaloneBinaryInputSize
    linarith only [hpLog,hn0,hm0,hB0]).trans hSN
  have hId : 10*(n:ℝ)+4≤14*N := (show 10*(n:ℝ)+4≤14*S by
    unfold S standaloneBinaryInputSize
    linarith only [hpLog,hInv0,hn0,hm0,hB0]).trans
      (mul_le_mul_of_nonneg_left hSN (by norm_num))
  have hLog : Real.log (1/(p.value:ℝ))≤N := (show Real.log (1/(p.value:ℝ))≤S by
    unfold S standaloneBinaryInputSize
    linarith only [hInv0,hn0,hm0,hB0]).trans hSN
  have hN0 : (n:ℝ)+m+B+2≤N := (show (n:ℝ)+m+B+2≤S by
    unfold S standaloneBinaryInputSize
    linarith only [hInv0,hpLog]).trans hSN
  let HC := exists_confidence_level hp.1 hp1
  let HCq := (exists_quarter_pow_le_ratCast p.value).mp HC
  have hs := countedBinaryStandalonePlan_spec y x hx h p hh ⟨hp.1,hp1⟩ HCq
  dsimp only at hs
  have hh2 : (h.value:ℝ)/2∈Ioo (0:ℝ) 1 := ⟨by linarith [hh.1],by linarith [hh.2]⟩
  let H := scalarPlannerPrecision_exists hβ hh2
  let δ := plannerGridTolerance n β (h.value:ℝ)
  have hδ : 0<δ := plannerGridTolerance_pos n (zero_lt_one.trans_le hβ) hh.1
  have hδ1 : δ<1 := plannerGridTolerance_lt_one n hβ hh.2.le
  let G := exists_confidence_level hδ hδ1
  have hLevel : q.level=(countedScalarPlannerLevel β ((h.value:ℝ)/2) H).1 := hs.1
  have hPrec : q.precision=(countedPlannerBitPrecision n β (h.value:ℝ) G).1 := hs.2.1
  have hTree : (16:ℝ)^q.level≤K*N^16 := by
    rw [hLevel]
    have hmul := mul_le_mul (hβE.trans hEN) hInv (by positivity) (zero_le_one.trans hN)
    have he : β/((h.value:ℝ)/2)=2*(β*(1/(h.value:ℝ))) := by ring
    calc
      _ ≤ (6400:ℝ)^4*(β/((h.value:ℝ)/2))^8 := countedScalarPlannerLevel_tree_factor hβ hh2 H
      _ ≤ (6400:ℝ)^4*(2*(N*N))^8 := by
        rw [he]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left hmul (by norm_num)) _) (by positivity)
      _ = _ := by
        have heN : (N*N)^8=N^16 := by
          rw [←pow_two,←pow_mul]
        rw [mul_pow,heN]
        exact (mul_assoc ((6400:ℝ)^4) ((2:ℝ)^8) (N^16)).symm
  have hGrid : (q.precision:ℝ)≤41*N^3 := by
    rw [hPrec]
    have hB := (countedPlannerBitPrecision_correct n hβ hh.1 hh.2.le G).2.2.1
    have hLog0 : 0≤Real.log (1/δ) :=
      Real.log_nonneg ((one_le_div hδ).mpr (by simpa only [one_mul] using hδ1.le))
    have hLogD : Real.log (1/δ)/Real.log 4≤1/δ :=
      (div_le_self hLog0 one_le_log_four).trans (Real.log_le_self (by positivity))
    have hmul : β*(10*(n:ℝ)+4)*(1/(h.value:ℝ))≤N*(14*N)*N :=
      mul_le_mul (mul_le_mul (hβE.trans hEN) hId (by positivity) (by positivity))
        hInv hInv0 (by positivity)
    have he : 2*(1/δ)=(8/3)*(β*(10*(n:ℝ)+4)*(1/(h.value:ℝ))) := by
      unfold δ plannerGridTolerance
      rw [div_div_eq_mul_div]
      ring
    calc
      _ ≤ 2*(Real.log (1/δ)/Real.log 4)+3 := hB.le
      _ ≤ 2*(1/δ)+3 := add_le_add (mul_le_mul_of_nonneg_left hLogD (by norm_num)) le_rfl
      _ ≤ (8/3)*(N*(14*N)*N)+3 := by
        rw [he]
        exact add_le_add (mul_le_mul_of_nonneg_left hmul (by norm_num)) le_rfl
      _ = (112/3)*N^3+3 := by ring
      _ ≤ 41*N^3 := by linarith only [one_le_pow₀ hN (n:=3)]
  have hCopy : (q.halfCopies:ℝ)≤2*N := by
    have h := confidenceCopyCount_log_bound hp.1 hp1 HC
    have e := confidenceCopyCount_ratCast p.value HCq HC
    have he : (confidenceCopyCount (p.value:ℝ) HC:ℝ)=2*(q.halfCopies:ℝ)+1 := by
      rw [e,confidenceCopyCount,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,hs.2.2]
    have hDiv : Real.log (1/(p.value:ℝ))/Real.log 4≤Real.log (1/(p.value:ℝ)) :=
      div_le_self hpLog one_le_log_four
    rw [he] at h
    linarith only [h,hDiv,hLog,hN]
  have h1 : N≤N^16 := by simpa only [pow_one] using pow_le_pow_right₀ hN (by decide : 1≤16)
  have h3 : N^3≤N^16 := pow_le_pow_right₀ hN (by decide)
  change ((n+m+B+q.precision+16^q.level+q.halfCopies+2:ℕ):ℝ)≤(K+100)*N^16
  push_cast
  have hSmall : (n:ℝ)+m+B≤N^16 :=
    (le_trans (by linarith only) hN0).trans h1
  have hTwo : (2:ℝ)≤2*N^16 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hN (n:=16)) (by norm_num : (0:ℝ)≤2)
  calc
    _ ≤ N^16+41*N^16+K*N^16+2*N^16+2*N^16 :=
      add_le_add (add_le_add (add_le_add (add_le_add hSmall
        (hGrid.trans (mul_le_mul_of_nonneg_left h3 (by norm_num)))) hTree)
        (hCopy.trans (mul_le_mul_of_nonneg_left h1 (by norm_num)))) hTwo
    _ = (K+46)*N^16 := by generalize N^16=d; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only) (by positivity)


/-- Explicit work bounds for all positive empirical counts. The
coefficient and degree are independent of the row lengths and data. -/
theorem standaloneBinaryWork_exponential_polynomial :
    ∃ C d : ℕ, ∀ {n : ℕ} {k : Fin n → ℕ} [∀ i, NeZero (k i)]
      (y : (i : Fin n) → Fin (k i) → BinaryRational) (hy : ∀ i j, 0≤((y i j).value:ℝ))
      (x : ScalarPlannerListState n BinaryRational) (_ : x.1.Nodup) (h p : BinaryRational)
      (_ : (h.value:ℝ)∈Ioo (0:ℝ) 1) (_ : (p.value:ℝ)∈Ioo (0:ℝ) (1/2)) (m B : ℕ),
      let L := (empiricalPlannerInstance (fun i j => ((y i j).value:ℝ)) hy).positiveCount
      let q := countedBinaryStandalonePlan (plannerStoredRows y) x h p
      (standaloneBinaryTotalWorkBound n m B q.precision q.level q.halfCopies:ℝ) ≤
        C*Real.exp ((4*(d:ℝ))*L)*(standaloneBinaryInputSize n m B (h.value:ℝ) (p.value:ℝ))^d := by
  obtain ⟨C,d,hBound⟩ := standaloneBinaryTotalWorkBound_polynomial
  let K : ℕ := 6400^4*2^8+100
  refine ⟨C*K^d,16*d,fun {n k} _ y hy x hx h p hh hp m B => ?_⟩
  dsimp only
  let L := (empiricalPlannerInstance (fun i j => ((y i j).value:ℝ)) hy).positiveCount
  let q := countedBinaryStandalonePlan (plannerStoredRows y) x h p
  let S := standaloneBinaryInputSize n m B (h.value:ℝ) (p.value:ℝ)
  have hs := standaloneBinarySchedule_size y hy x hx h p hh hp m B
  dsimp only at hs
  have hb := hBound n m B q.precision q.level q.halfCopies
  have hR : (standaloneBinaryTotalWorkBound n m B q.precision q.level q.halfCopies:ℝ)≤
      (C:ℝ)*((n+m+B+q.precision+16^q.level+q.halfCopies+2:ℕ):ℝ)^d := by exact_mod_cast hb
  have hPow : ((Real.exp (4*L))^((16:ℕ)*d)) = Real.exp ((4*((16*d:ℕ):ℝ))*L) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ _ := hR
    _ ≤ (C:ℝ)*((K:ℝ)*(S*Real.exp (4*L))^16)^d := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      simpa only [K,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,S,L,q] using hs
    _ = _ := by
      rw [mul_pow,←pow_mul,mul_pow,hPow]
      push_cast
      ac_rfl

/-- Paper label `thm:scalar-planner`. The empirical rows may have
different positive lengths. The bound covers native binary work and
fair draws for every outcome, without a positive-count cutoff. -/
theorem standaloneBinaryScalarPlanner :
    ∃ C d : ℕ, ∀ {n : ℕ} {k : Fin n → ℕ} [∀ i, NeZero (k i)]
      (y : (i : Fin n) → Fin (k i) → BinaryRational)
      (hy : ∀ i j, 0≤((y i j).value:ℝ)) (_ : ∀ i j, ((y i j).value:ℝ)≤1)
      (x : ScalarPlannerListState n BinaryRational) (_ : x.1.Nodup)
      (_ : (x.2.1.value:ℝ)∈Icc (0:ℝ) 1) (_ : (x.2.2.value:ℝ)∈Icc (0:ℝ) 4)
      (h p : BinaryRational) (_ : (h.value:ℝ)∈Ioo (0:ℝ) 1) (_ : (p.value:ℝ)∈Ioo (0:ℝ) (1/2))
      (m B : ℕ) (_ : 2≤B) (_ : ∀ i, k i≤m) (_ : ∀ i j, RationalHeight (y i j).value B)
      (_ : RationalHeight x.2.1.value B) (_ : RationalHeight x.2.2.value B)
      (_ : RationalHeight h.value B) (_ : RationalHeight p.value B),
      let rows := plannerStoredRows y
      let plan := countedBinaryStandalonePlan rows x h p
      let Q := empiricalPlannerInstance (fun i j => ((y i j).value:ℝ)) hy
      let v := Q.continuationValue x.1.toFinset (x.2.1.value:ℝ) 1 (x.2.2.value:ℝ)
      let est := fun bits : StandaloneRawBits n plan =>
        ((countedBinaryStandaloneFromBits rows x h p bits).value.value:ℝ)
      Measurable est ∧
      (standaloneRawBitLaw n plan).real {bits | (h.value:ℝ)< |est bits-v|}≤(p.value:ℝ) ∧
      ∀ bits : StandaloneRawBits n plan,
        ((countedBinaryStandaloneFromBits rows x h p bits).work:ℝ)≤
          C*Real.exp ((4*(d:ℝ))*Q.positiveCount)*(standaloneBinaryInputSize n m B (h.value:ℝ) (p.value:ℝ))^d := by
  obtain ⟨C,d,hBound⟩ := standaloneBinaryWork_exponential_polynomial
  refine ⟨C,d,fun {n k} _ y hy hcap x hx hu hz h p hh hp m B hB hk hY hU hZ hH hP => ?_⟩
  dsimp only
  let rows := plannerStoredRows y
  let plan := countedBinaryStandalonePlan rows x h p
  let Q := empiricalPlannerInstance (fun i j => ((y i j).value:ℝ)) hy
  let v := Q.continuationValue x.1.toFinset (x.2.1.value:ℝ) 1 (x.2.2.value:ℝ)
  let est := fun seed : StandaloneBinarySeed n plan =>
    ((countedBinaryStandaloneQuery rows x h p seed).value.value:ℝ)
  have hC := countedBinaryStandaloneQuery_correct y hy hcap x hx h p hh hp m B hB hk hY hU hZ
  dsimp only at hC
  have hV : scalarPlannerValue (fun i j => ((y i j).value:ℝ)) hy
      (scalarPlannerListInterpret (scalarPlannerStateRatCast (scalarPlannerStateValueMap BinaryRational.value x)))=v :=
    scalarPlannerValue_eq_continuation _ _ _ hu hz
  rw [hV] at hC
  have hMP := measurePreserving_standaloneSeedFromBits n plan
  refine ⟨?_,?_,?_⟩
  · simp_rw [countedBinaryStandaloneFromBits_value]
    exact hC.1.comp hMP.measurable
  · simp_rw [countedBinaryStandaloneFromBits_value]
    let E := {seed : StandaloneBinarySeed n plan | (h.value:ℝ)< |est seed-v|}
    have hE : MeasurableSet E := measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (hC.1.sub_const v))
    change (standaloneRawBitLaw n plan).real ((standaloneSeedFromBits n plan) ⁻¹' E)≤_
    rw [←map_measureReal_apply hMP.measurable hE,hMP.map_eq]
    exact hC.2
  · intro bits
    have hRows (i : Fin n) : (rows.get i).length≤m := by
      simpa only [rows,plannerStoredRows_get,List.length_ofFn] using hk i
    have hData (i : Fin n) (a : BinaryRational) (ha : a∈rows.get i) : RationalHeight a.value B := by
      rw [show rows.get i=List.ofFn (y i) from plannerStoredRows_get y i] at ha
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
      exact hY i j
    have hW := countedBinaryStandaloneFromBits_work rows x h p m B hB hRows hData hx hU hZ hH hP bits
    dsimp only at hW
    exact (Nat.cast_le.mpr hW).trans (hBound y hy x hx h p hh hp m B)

end ProphetSecretary.Statistics
