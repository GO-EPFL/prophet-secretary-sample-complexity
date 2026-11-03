import ProphetSecretary.Statistics.BinaryCalibrationSelection
import ProphetSecretary.Statistics.BinaryCalibrationMixture

/-!
# Binary calibration selection

The duration arrays are averaged once to form the knots. A single
first-crossing scan, interpolation and dyadic comparison choose the
policy coefficient.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability
open CalibrationBinaryExpr

variable {m J : ℕ}

def countedBinaryCalibrationKnot (invM : CalibrationBinary)
    (duration : Fin m → Array CalibrationBinary) (J k : ℕ) : CalibrationBinary×ℕ :=
  if k=0 then (0,2) else if k≤J+1 then
    let q := (binaryDurationKnot invM (List.ofFn fun r : Fin m =>
      ((duration r)[k-1]?).getD 1)).evaluate
    (q.1,q.2+2*m+3)
  else (1,3)

private lemma durationRead_value (v : Array CalibrationBinary) (k : ℕ) :
    (v[k]?.getD 1).value=((v.map BinaryRational.value)[k]?).getD 1 := by
  rw [Array.getElem?_map]
  cases v[k]? <;> simp

lemma countedBinaryCalibrationKnot_value (invM : CalibrationBinary)
    (duration : Fin m → Array CalibrationBinary) (J k : ℕ) (hi : invM.value=(m:ℚ)⁻¹) :
    (countedBinaryCalibrationKnot invM duration J k).1.value =
      (((countedCalibrationKnots (fun r => (duration r).map BinaryRational.value) J)[k]?).getD 1) := by
  by_cases hk : k<J+3
  · rw [countedCalibrationKnots,Array.getElem?_ofFn,dif_pos hk,Option.getD_some]
    change _=(if k=0 then 0 else if k≤J+1 then
      (m:ℚ)⁻¹ * ∑ r : Fin m, (((duration r).map BinaryRational.value)[k-1]?).getD 1 else 1)
    by_cases h0 : k=0
    · simp [countedBinaryCalibrationKnot,h0]
    · by_cases h1 : k≤J+1
      · simp only [countedBinaryCalibrationKnot,h0,if_false,h1,if_true,binaryDurationKnot_value,hi,
          List.map_ofFn,Function.comp_def,durationRead_value,List.sum_ofFn]
      · simp [countedBinaryCalibrationKnot,h0,h1]
  · have h0 : k≠0 := by omega
    have h1 : ¬k≤J+1 := by omega
    simp [countedCalibrationKnots,countedBinaryCalibrationKnot,hk,h0,h1]

lemma countedBinaryCalibrationKnot_height (invM : CalibrationBinary)
    (duration : Fin m → Array CalibrationBinary) (J k B : ℕ) (hi : RationalHeight invM.value B)
    (h : ∀ (r : Fin m) (j : ℕ),RationalHeight (((duration r)[j]?.getD 1 : CalibrationBinary).value) B) :
    RationalHeight (countedBinaryCalibrationKnot invM duration J k).1.value ((2*m+3)*(B+1)) := by
  unfold countedBinaryCalibrationKnot
  split_ifs
  · rw [BinaryRational.zero_value]
    exact rationalHeight_zero.mono (Nat.zero_le _)
  · dsimp only
    rw [evaluate_value]
    let l := List.ofFn fun r : Fin m => ((duration r)[k-1]?).getD 1
    have hL : ∀ x∈l,RationalHeight x.value B := by
      intro x hx
      obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hx
      exact h r _
    have hh := (binaryDurationKnot invM l).value_height B ⟨hi,binaryDurationSum_leaves l B hL⟩
    rw [binaryDurationKnot_size,List.length_ofFn] at hh
    exact hh
  · rw [BinaryRational.one_value]
    exact rationalHeight_one.mono (Nat.zero_le _)

def binaryCalibrationKnotWork (m B : ℕ) : ℕ :=
  (2*m+3)*workUnit (2*m+3) B+2*m+3

lemma countedBinaryCalibrationKnot_work (invM : CalibrationBinary)
    (duration : Fin m → Array CalibrationBinary) (J k B : ℕ) (hi : RationalHeight invM.value B)
    (h : ∀ (r : Fin m) (j : ℕ),RationalHeight (((duration r)[j]?.getD 1 : CalibrationBinary).value) B) :
    (countedBinaryCalibrationKnot invM duration J k).2≤binaryCalibrationKnotWork m B := by
  unfold countedBinaryCalibrationKnot binaryCalibrationKnotWork
  split_ifs
  · dsimp only
    omega
  · let l := List.ofFn fun r : Fin m => ((duration r)[k-1]?).getD 1
    have hL : ∀ x∈l,RationalHeight x.value B := by
      intro x hx
      obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hx
      exact h r _
    have hh := binaryDurationKnot_work invM l B hi hL
    rw [List.length_ofFn] at hh
    change (binaryDurationKnot invM l).evaluate.2+2*m+3≤_
    omega
  · dsimp only
    omega

/-- The array of knot values is materialized once. Subsequent indexed reads
in the scan and the interpolation do not recompute validation means. -/
def countedBinaryCalibrationKnots (invM : CalibrationBinary)
    (duration : Fin m → Array CalibrationBinary) (J : ℕ) : Array CalibrationBinary×ℕ :=
  let q := Array.ofFn fun k : Fin (J+3) => countedBinaryCalibrationKnot invM duration J k.val
  (q.map Prod.fst,(q.toList.map (fun z => z.2+2)).sum+1)

lemma countedBinaryCalibrationKnots_get (invM : CalibrationBinary)
    (duration : Fin m → Array CalibrationBinary) (J k : ℕ) :
    ((countedBinaryCalibrationKnots invM duration J).1[k]?).getD 1 =
      (countedBinaryCalibrationKnot invM duration J k).1 := by
  by_cases h : k<J+3
  · simp [countedBinaryCalibrationKnots,Array.map_ofFn,h]
  · have h0 : k≠0 := by omega
    have h1 : ¬k≤J+1 := by omega
    simp [countedBinaryCalibrationKnots,Array.map_ofFn,countedBinaryCalibrationKnot,h,h0,h1]

lemma countedBinaryCalibrationKnots_work (invM : CalibrationBinary)
    (duration : Fin m → Array CalibrationBinary) (J B : ℕ) (hi : RationalHeight invM.value B)
    (h : ∀ (r : Fin m) (j : ℕ),RationalHeight (((duration r)[j]?.getD 1 : CalibrationBinary).value) B) :
    (countedBinaryCalibrationKnots invM duration J).2≤
      (J+3)*(binaryCalibrationKnotWork m B+2)+1 := by
  simp only [countedBinaryCalibrationKnots,Array.toList_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  have hh : ∑ k : Fin (J+3), ((countedBinaryCalibrationKnot invM duration J k.val).2+2)
      ≤ ∑ _ : Fin (J+3), (binaryCalibrationKnotWork m B+2) :=
    Finset.sum_le_sum (fun _ _ => Nat.add_le_add_right (countedBinaryCalibrationKnot_work _ _ _ _ _ hi h) _)
  simpa only [Finset.sum_const,Fintype.card_fin,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using Nat.add_le_add_right hh 1

structure BinaryCalibrationSelection (J : ℕ) where
  segment : ℕ
  fraction : CalibrationBinary
  selected : Fin (J+1)
  work : ℕ

def countedBinaryCalibrationSelection (invM rho scale : CalibrationBinary)
    (last coin : List Bool) (duration : Fin m → Array CalibrationBinary) (J : ℕ) :
    BinaryCalibrationSelection J :=
  let a := countedBinaryCalibrationKnots invM duration J
  let v := fun k : ℕ => (a.1[k]?).getD (1:CalibrationBinary)
  let k := countedBinaryKnotScan v rho 0 (J+2)
  let p := (binaryInterpolation rho (v (k.1-1)) (v k.1)).evaluate
  let q := countedCalibrationMixture scale p.1 last coin
  ⟨k.1,p.1,if q.1 then upperPolicyIndex J k.1 else lowerPolicyIndex J k.1,a.2+k.2+p.2+q.2+8⟩

theorem countedBinaryCalibrationSelection_value (invM rho scale : CalibrationBinary)
    (last coin : List Bool) (duration : Fin m → Array CalibrationBinary) (J N : ℕ) (hN : 0<N)
    (hi : invM.value=(m:ℚ)⁻¹) (hs : scale.value=(N:ℚ)) (hl : binaryWordValue last=N-1) :
    let a := countedCalibrationKnots (fun r => (duration r).map BinaryRational.value) J
    let v := fun k : ℕ => (a[k]?).getD (1:ℚ)
    let k := (countedKnotScan v rho.value 0 (J+2)).1
    let f := (rho.value-v (k-1))/(v k-v (k-1))
    let q := countedBinaryCalibrationSelection invM rho scale last coin duration J
    q.segment=k ∧ q.fraction.value=f ∧
    q.selected=(if (binaryWordValue coin:ℚ)/(N:ℚ)<rationalMixtureGridRound N hN f then
      upperPolicyIndex J k else lowerPolicyIndex J k) := by
  let a := countedCalibrationKnots (fun r => (duration r).map BinaryRational.value) J
  let v := fun k : ℕ => (a[k]?).getD (1:ℚ)
  let A := countedBinaryCalibrationKnots invM duration J
  let V := fun k : ℕ => (A.1[k]?).getD (1:CalibrationBinary)
  have hV : (fun k => (V k).value)=v := by
    funext k
    exact (congrArg BinaryRational.value (countedBinaryCalibrationKnots_get _ _ _ _)).trans
      (countedBinaryCalibrationKnot_value _ _ _ _ hi)
  let k := (countedKnotScan v rho.value 0 (J+2)).1
  let K := (countedBinaryKnotScan V rho 0 (J+2)).1
  have hK : K=k := by
    change (countedBinaryKnotScan V rho 0 (J+2)).1=_
    rw [countedBinaryKnotScan_value,hV]
  let p := (binaryInterpolation rho (V (K-1)) (V K)).evaluate.1
  have hp : p.value=(rho.value-v (k-1))/(v k-v (k-1)) := by
    dsimp only [p]
    rw [binaryInterpolation_value,hK,congrFun hV,congrFun hV]
  refine ⟨hK,hp,?_⟩
  change (if (countedCalibrationMixture scale p last coin).1 then upperPolicyIndex J K else lowerPolicyIndex J K)=
    (if (binaryWordValue coin:ℚ)/(N:ℚ)<rationalMixtureGridRound N hN ((rho.value-v (k-1))/(v k-v (k-1)))
      then upperPolicyIndex J k else lowerPolicyIndex J k)
  rw [countedCalibrationMixture_value _ _ _ _ N hN hs hl,hp,hK]
  split_ifs <;> simp_all

def binaryCalibrationSelectionWork (m J B : ℕ) : ℕ :=
  let A := (2*m+3)*(B+1)
  let H := 7*(A+1)
  (J+3)*(binaryCalibrationKnotWork m B+2)+1+
    (1+(J+2)*(calibrationComparisonWork A+4))+7*workUnit 7 A+
    (3600*(H+2)^3+60*(2*H+2)^2+2*(16*(2*H+1)+12)+4)+8

theorem countedBinaryCalibrationSelection_work (invM rho scale : CalibrationBinary)
    (last coin : List Bool) (duration : Fin m → Array CalibrationBinary) (J B : ℕ)
    (hi : RationalHeight invM.value B) (hr : RationalHeight rho.value B) (hs : RationalHeight scale.value B)
    (hl : last.length≤B) (hc : coin.length≤B)
    (h : ∀ (r : Fin m) (j : ℕ),RationalHeight (((duration r)[j]?.getD 1 : CalibrationBinary).value) B) :
    (countedBinaryCalibrationSelection invM rho scale last coin duration J).work≤
      binaryCalibrationSelectionWork m J B := by
  let A := (2*m+3)*(B+1)
  let H := 7*(A+1)
  have hBA : B≤A := by
    have hh := Nat.le_mul_of_pos_left (B+1) (show 0<2*m+3 by omega)
    unfold A
    omega
  have hAH : A≤H := by dsimp [H]; omega
  let a := countedBinaryCalibrationKnots invM duration J
  let v := fun k : ℕ => (a.1[k]?).getD (1:CalibrationBinary)
  have hv (k : ℕ) : RationalHeight (v k).value A := by
    unfold v a
    rw [countedBinaryCalibrationKnots_get]
    exact countedBinaryCalibrationKnot_height _ _ _ _ _ hi h
  let k := countedBinaryKnotScan v rho 0 (J+2)
  let p := (binaryInterpolation rho (v (k.1-1)) (v k.1)).evaluate
  have hP : RationalHeight p.1.value H := by
    unfold p
    rw [evaluate_value]
    exact (binaryInterpolation rho (v (k.1-1)) (v k.1)).value_height A
      ⟨⟨hr.mono hBA,hv _⟩,⟨hv _,hv _⟩⟩
  have ha := countedBinaryCalibrationKnots_work invM duration J B hi h
  have hk := countedBinaryKnotScan_work v rho 0 (J+2) A (hr.mono hBA) hv
  have hp := binaryInterpolation_work rho (v (k.1-1)) (v k.1) A (hr.mono hBA) (hv _) (hv _)
  have hq := countedCalibrationMixture_work scale p.1 last coin H (hs.mono (hBA.trans hAH))
    hP (hl.trans (hBA.trans hAH)) (hc.trans (hBA.trans hAH))
  change a.2+k.2+p.2+(countedCalibrationMixture scale p.1 last coin).2+8≤_
  change a.2≤_ at ha
  change k.2≤_ at hk
  change p.2≤_ at hp
  change _≤(J+3)*(binaryCalibrationKnotWork m B+2)+1+
    (1+(J+2)*(calibrationComparisonWork A+4))+7*workUnit 7 A+
    (3600*(H+2)^3+60*(2*H+2)^2+2*(16*(2*H+1)+12)+4)+8
  omega

end ProphetSecretary.Statistics.Calibration
