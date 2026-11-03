import ProphetSecretary.Statistics.CalibratedOuter.NativeLearner

/-!
# Native reward on rational observation laws

Rational observations may have arbitrary countable support. Casting them to
the real model preserves the independent online and sample product laws.
The native reward uses the original value at the first acceptance.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

structure RationalOfferInstance (n : ℕ) where
  law : Fin n → Measure ℚ
  probability : ∀ i, IsProbabilityMeasure (law i)
  nonnegative : ∀ i, ∀ᵐ x ∂law i, 0≤x

attribute [instance] RationalOfferInstance.probability

variable {n m : ℕ}

private lemma measurable_ratReal : Measurable (fun x : ℚ => (x : ℝ)) := measurable_of_countable _

noncomputable def RationalOfferInstance.toInstance (P : RationalOfferInstance n) : Instance n where
  law i := (P.law i).map (fun x : ℚ => (x : ℝ))
  probability _ := Measure.isProbabilityMeasure_map measurable_ratReal.aemeasurable
  nonnegative i := by
    apply (ae_map_iff measurable_ratReal.aemeasurable measurableSet_Ici).mpr
    filter_upwards [P.nonnegative i] with x hx
    exact_mod_cast hx

noncomputable def RationalOfferInstance.valuesLaw (P : RationalOfferInstance n) : Measure (Fin n → ℚ) :=
  Measure.pi P.law

noncomputable def RationalOfferInstance.samplesLaw (P : RationalOfferInstance n) (k : ℕ) :
    Measure (Fin n → Fin k → ℚ) :=
  Measure.pi fun i => Measure.pi fun _ => P.law i

instance RationalOfferInstance.valuesLaw_probability (P : RationalOfferInstance n) :
    IsProbabilityMeasure P.valuesLaw := by unfold RationalOfferInstance.valuesLaw; infer_instance

instance RationalOfferInstance.samplesLaw_probability (P : RationalOfferInstance n) (k : ℕ) :
    IsProbabilityMeasure (P.samplesLaw k) := by unfold RationalOfferInstance.samplesLaw; infer_instance

lemma RationalOfferInstance.cast_values_measurePreserving (P : RationalOfferInstance n) :
    MeasurePreserving (fun x : Fin n → ℚ => fun i => (x i : ℝ)) P.valuesLaw P.toInstance.valuesLaw :=
  measurePreserving_pi _ _ (fun _ => ⟨measurable_ratReal,rfl⟩)

lemma RationalOfferInstance.cast_samples_measurePreserving (P : RationalOfferInstance n) (k : ℕ) :
    MeasurePreserving (fun y : Fin n → Fin k → ℚ => fun i j => (y i j : ℝ))
      (P.samplesLaw k) (P.toInstance.reservoirLaw k) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_pi _ _ (fun _ => ⟨measurable_ratReal,rfl⟩))

def rationalRankHistory (p : Equiv.Perm (Fin n)) (x : Fin n → ℚ) (k : Fin n) :
    Fin n → Option (Fin n × ℚ) := fun j => if p.symm j<k then some (p.symm j,x j) else none

lemma rationalRankHistory_cast (p : Equiv.Perm (Fin n)) (x : Fin n → ℚ) (k : Fin n) :
    calibrationRankHistoryCast (rationalRankHistory p x k)=rankHistory p (fun i => (x i : ℝ)) k := by
  funext j
  unfold calibrationRankHistoryCast rationalRankHistory rankHistory
  split_ifs <;> rfl

lemma rationalRankHistory_currentRank (p : Equiv.Perm (Fin n)) (x : Fin n → ℚ) (k i : Fin n) :
    onlineQueryRank (rationalRankHistory p x k) i=k := by
  unfold onlineQueryRank
  have h : (Finset.univ.filter (fun j => (rationalRankHistory p x k j).isSome=true)) =
      Finset.univ.filter (fun j => p.symm j<k) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,rationalRankHistory]
    by_cases he : p.symm j<k <;> simp [he]
  rw [h,card_filter_permutation_lt,clockHistoryRank_of_fin]

namespace FairCalibrationParameters

noncomputable def nativeAccepted (a : FairCalibrationParameters n m) (mu zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) (seed : a.NativeOuterSeed zlo hz) (y : Fin n → Fin (outerSampleBudget m) → ℚ)
    (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  let Y := outerRawBlocks y
  let T := a.nativeTargetSchedule
  let P := a.nativeThresholdSchedule zlo hz
  let q := countedFiniteOuterPrepare (by have := a.two_le; omega : 1≤m) T P
    a.clockBits a.coinBits (outerMarkBits n m) mu zlo (1/4) (nativeCalibrationCutoff m)
    (fun r i => Y.1 i r) (fun r i => Y.2.1 i r) (fun r i => Y.2.2 i r) seed.1 seed.2
  Finset.univ.filter fun i =>
    (countedFiniteOuterDecision P zlo (1/4) q (p.symm i) i (x i) (rationalRankHistory p x (p.symm i))).1=true

/-- Analytical reward of the causal native decisions, with zero if every
candidate is rejected. -/
noncomputable def nativeReward (a : FairCalibrationParameters n m) (mu zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) (seed : a.NativeOuterSeed zlo hz) (y : Fin n → Fin (outerSampleBudget m) → ℚ)
    (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) : ℝ :=
  let A := a.nativeAccepted mu zlo hz seed y x p
  ∑ i : Fin n, if i∈A ∧ (∀ j∈A, p.symm i≤p.symm j) then (x i : ℝ) else 0

theorem nativeReward_eq (a : FairCalibrationParameters n m) (mu zlo : ℚ) (hz : (zlo : ℝ)=a.zlo)
    (seed : a.NativeOuterSeed zlo hz) (y : Fin n → Fin (outerSampleBudget m) → ℚ)
    (x : Fin n → ℚ) (p : Equiv.Perm (Fin n)) :
    let L := outerFairRankLearner (by have := a.two_le; omega : 1≤m)
      (a.finiteLearner (mu : ℝ)) (outerMarkBits n m)
    a.nativeReward mu zlo hz seed y x p =
      L.policy.reward ((fun i j => (y i j : ℝ)),seed.1,a.nativeCalibrationBitsToMeasured zlo hz seed.2)
        p (fun i => (x i : ℝ)) := by
  dsimp only
  let L := outerFairRankLearner (by have := a.two_le; omega : 1≤m)
    (a.finiteLearner (mu : ℝ)) (outerMarkBits n m)
  let r : Reservoir n (outerSampleBudget m) × L.Seed :=
    ((fun i j => (y i j : ℝ)),seed.1,a.nativeCalibrationBitsToMeasured zlo hz seed.2)
  let X := fun i => (x i : ℝ)
  have h : a.nativeAccepted mu zlo hz seed y x p=L.policy.accepted r p X := by
    ext i
    unfold nativeAccepted
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,RankPolicy.mem_accepted,RankPolicy.action]
    rw [a.nativeFiniteOuterDecision_eq mu zlo hz y seed.1 seed.2 (p.symm i) i (x i)
      (rationalRankHistory p x (p.symm i)) (rationalRankHistory_currentRank p x (p.symm i) i),
      rationalRankHistory_cast]
  unfold nativeReward RankPolicy.reward
  dsimp only
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  have hSel : L.policy.Selects r p X i ↔
      i∈L.policy.accepted r p X ∧ (∀ j∈L.policy.accepted r p X, p.symm i≤p.symm j) := Iff.rfl
  change (if i∈L.policy.accepted r p X ∧ (∀ j∈L.policy.accepted r p X, p.symm i≤p.symm j)
    then (x i : ℝ) else 0)=(if L.policy.Selects r p X i then (x i : ℝ) else 0)
  by_cases hi : L.policy.Selects r p X i
  · rw [if_pos (hSel.mp hi),if_pos hi]
  · rw [if_neg (mt hSel.mpr hi),if_neg hi]

local instance nativeOuterSeed_probability (a : FairCalibrationParameters n m) (zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) : IsProbabilityMeasure (a.nativeOuterSeedLaw zlo hz) := by
  unfold nativeOuterSeedLaw
  infer_instance

noncomputable def nativeExpectedReward (a : FairCalibrationParameters n m) (mu zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) (P : RationalOfferInstance n) : ℝ :=
  ∫ w : (Fin n → ℚ) × (Equiv.Perm (Fin n) × ((Fin n → Fin (outerSampleBudget m) → ℚ) × a.NativeOuterSeed zlo hz)),
    a.nativeReward mu zlo hz w.2.2.2 w.2.2.1 w.1 w.2.1
      ∂P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod
        ((P.samplesLaw (outerSampleBudget m)).prod (a.nativeOuterSeedLaw zlo hz)))

theorem nativeExpectedReward_eq (a : FairCalibrationParameters n m) (mu zlo : ℚ)
    (hz : (zlo : ℝ)=a.zlo) (P : RationalOfferInstance n) :
    a.nativeExpectedReward mu zlo hz P =
      (outerFairRankLearner (by have := a.two_le; omega : 1≤m)
        (a.finiteLearner (mu : ℝ)) (outerMarkBits n m)).expectedReward P.toInstance := by
  let L := outerFairRankLearner (by have := a.two_le; omega : 1≤m)
    (a.finiteLearner (mu : ℝ)) (outerMarkBits n m)
  let π := L.randomizedPolicy P.toInstance
  let A := (Fin n → ℚ) × (Equiv.Perm (Fin n) × ((Fin n → Fin (outerSampleBudget m) → ℚ) × a.NativeOuterSeed zlo hz))
  let ν := P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod
    ((P.samplesLaw (outerSampleBudget m)).prod (a.nativeOuterSeedLaw zlo hz)))
  let f : A → π.World := fun w =>
    ((fun i => (w.1 i : ℝ)),w.2.1,(fun i j => (w.2.2.1 i j : ℝ)),
      w.2.2.2.1,a.nativeCalibrationBitsToMeasured zlo hz w.2.2.2.2)
  have hS := a.nativeOuterSeed_measurePreserving mu zlo hz
  have h : MeasurePreserving f ν (π.worldLaw P.toInstance) :=
    P.cast_values_measurePreserving.prod ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod
      ((P.cast_samples_measurePreserving _).prod hS))
  calc
    _ = ∫ w : A, π.realizedReward (f w) ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ (fun w => a.nativeReward_eq mu zlo hz w.2.2.2 w.2.2.1 w.1 w.2.1)
    _ = _ := h.hasLaw.integral_comp π.measurable_realizedReward.aestronglyMeasurable

end FairCalibrationParameters

/-- The native execution's expected reward has the same worst-case
sample guarantee for rational observation laws. -/
theorem native_finite_bit_sample_upper_bound :
    ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (zInv : ℕ)
      (hInv : 1/((1-(b : ℝ))/(b : ℝ))≤(zInv : ℝ)) (A eps0 : ℝ),
      0<A ∧ 0<eps0 ∧ ∀ eps∈Ioo (0 : ℝ) eps0,
        ∃ (m : ℕ) (hm : 2≤m), (outerSampleBudget m : ℝ)≤A/eps ∧
          ∀ (n : ℕ) (hn : 0<n) (P : RationalOfferInstance n), P.toInstance.HasPositiveFiniteMaximum →
            let a : FairCalibrationParameters n m :=
              ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
            let zlo : ℚ := (1-b)/b
            let hz : (zlo : ℝ)=a.zlo := by
              change ((((1-b)/b : ℚ) : ℝ))=(1-(b : ℝ))/(b : ℝ)
              simp only [Rat.cast_div,Rat.cast_sub,Rat.cast_one]
            (optimalCompetitiveRatio-eps)*P.toInstance.expectedMaximum ≤
              a.nativeExpectedReward (1/10000000) zlo hz P := by
  obtain ⟨b,hb,zInv,hInv,A,eps0,hA,heps,hBound⟩ := finite_bit_outer_sample_upper_bound
  refine ⟨b,hb,zInv,hInv,A,eps0,hA,heps,?_⟩
  intro eps he
  obtain ⟨m,hm,hB,hR⟩ := hBound eps he
  refine ⟨m,hm,hB,?_⟩
  intro n hn P hP
  dsimp only
  rw [FairCalibrationParameters.nativeExpectedReward_eq,
    show ((1/10000000 : ℚ) : ℝ)=1/10000000 by norm_num]
  exact hR n hn P.toInstance hP

end ProphetSecretary.Statistics.Calibration
