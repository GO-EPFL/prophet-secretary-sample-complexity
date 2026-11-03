import ProphetSecretary.Statistics.ScalarPlannerSeedBank
import ProphetSecretary.Statistics.PlannerPolynomialWeight
import ProphetSecretary.Statistics.CalibratedPolicyCoupling
import ProphetSecretary.Statistics.CalibratedTargetCalls

/-!
# Scalar planner calls used by calibration

The positive-count guard makes the available query levels polynomially
bounded, uniformly over the first sample block and the unseen identities.
The target and threshold queries use different error and confidence levels.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} [NeZero m]

def calibrationWeightBound (m : ℕ) : ℝ := (4 : ℝ)^8*(2*(m : ℝ))^32

lemma calibrationWeightBound_ge_one : 1 ≤ calibrationWeightBound m := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  unfold calibrationWeightBound
  exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by linarith))

lemma planner_empirical_eq (y : Reservoir n m) (hy : ∀ i j, 0 ≤ y i j) :
    empiricalPlannerInstance (k := fun _ => m) y hy = totalEmpiricalInstance y := by
  apply Instance.eq_of_law_eq
  funext i
  change empiricalLaw (y i) = empiricalLaw (nonnegativeReservoir y i)
  rw [nonnegativeReservoir_eq y hy]

lemma scalarPlannerWeight_le_calibrationBound (y : Reservoir n m)
    (hy : ∀ i j, 0 ≤ y i j)
    (hc : (totalEmpiricalInstance y).positiveCount ≤ targetCountCutoff m) (A : Finset (Fin n)) :
    scalarPlannerWeight (k := fun _ => m) y A ≤ calibrationWeightBound m := by
  have hp (i : Fin n) : plannerPositiveProbability (k := fun _ => m) y i =
      ((totalEmpiricalInstance y).law i).real (Ioi 0) := by
    rw [← planner_empirical_eq y hy]
    exact (empiricalLaw_positiveProbability (y i)).symm
  have hs : (∑ i ∈ plannerActive (k := fun _ => m) y A, plannerPositiveProbability y i) ≤
      (totalEmpiricalInstance y).positiveCount := by
    calc
      _ ≤ ∑ i : Fin n, plannerPositiveProbability y i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ =>
          plannerPositiveProbability_nonnegative y i)
      _ = _ := Finset.sum_congr rfl (fun i _ => hp i)
  exact plannerWeight_le_polynomial _ _ (fun i _ => plannerPositiveProbability_nonnegative y i)
    (NeZero.pos m) (hs.trans hc)

noncomputable def calibrationPlannerLevel (m : ℕ) (h : ℝ) : ℕ :=
  scalarPlannerLevel (calibrationWeightBound m) h

lemma calibrationPlannerLevel_error {β h : ℝ} (hβ : 0 ≤ β) (hb : β ≤ calibrationWeightBound m)
    (hh : h ∈ Ioo (0 : ℝ) 1) :
    25*β^2*(1/2 : ℝ)^calibrationPlannerLevel m h ≤ h^2/64 := by
  apply le_trans _ (scalarPlannerLevel_error (calibrationWeightBound_ge_one (m := m)) hh)
  unfold calibrationPlannerLevel
  gcongr

abbrev CalibrationPlannerSeed (n m : ℕ) (h p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :=
  ScalarPlannerSeedBank n (calibrationPlannerLevel m h)
    (confidenceCopyCount p (exists_confidence_level hp.1 hp.2))

noncomputable def calibrationPlannerSeedLaw (n m : ℕ) (h p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Measure (CalibrationPlannerSeed n m h p hp) :=
  scalarPlannerSeedBankLaw _ _ _

instance (n m : ℕ) (h p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    IsProbabilityMeasure (calibrationPlannerSeedLaw n m h p hp) := by
  unfold calibrationPlannerSeedLaw
  infer_instance

noncomputable def calibrationPlannerCall (h p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContinuationEstimator n m (CalibrationPlannerSeed n m h p hp) :=
  fun y A u z s => scalarPlannerBankQuery (calibrationPlannerLevel m h) h p
    (exists_confidence_level hp.1 hp.2) y (A,(u,z)) s

omit [NeZero m] in
set_option maxHeartbeats 800000 in
theorem measurable_calibrationPlannerCall (h p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × CalibrationPlannerSeed n m h p hp))) =>
      calibrationPlannerCall h p hp q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  let Ω := Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × CalibrationPlannerSeed n m h p hp)))
  have hA : Measurable (fun q : Ω => q.2.1) := measurable_fst.comp measurable_snd
  have hu : Measurable (fun q : Ω => q.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hz : Measurable (fun q : Ω => q.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hs : Measurable (fun q : Ω => q.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hin : Measurable (fun q : Ω => ((q.1,(q.2.1,(q.2.2.1,q.2.2.2.1))),q.2.2.2.2)) :=
    (measurable_fst.prodMk (hA.prodMk (hu.prodMk hz))).prodMk hs
  let X := ScalarPlannerDataState n (fun _ => m) × CalibrationPlannerSeed n m h p hp
  let f : X → ℝ := fun q => scalarPlannerBankQuery (calibrationPlannerLevel m h) h p
    (exists_confidence_level hp.1 hp.2) q.1.1 q.1.2 q.2
  let g : Ω → X := fun q => ((q.1,(q.2.1,(q.2.2.1,q.2.2.2.1))),q.2.2.2.2)
  change Measurable (f ∘ g)
  have hf : Measurable f := measurable_scalarPlannerBankQuery (n := n) (k := fun _ => m)
    (calibrationPlannerLevel m h) h p (exists_confidence_level hp.1 hp.2)
  have hg : Measurable g := hin
  exact hf.comp hg

theorem calibrationPlannerCall_correct (h p : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioo (0 : ℝ) 1) (y : Reservoir n m) (hy : ∀ i j, y i j ∈ Icc (0 : ℝ) 1)
    (hc : (totalEmpiricalInstance y).positiveCount ≤ targetCountCutoff m)
    (A : Finset (Fin n)) (u z : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 4) :
    (calibrationPlannerSeedLaw n m h p hp).real {s | h < |calibrationPlannerCall h p hp y A u z s -
      (totalEmpiricalInstance y).continuationValue A u 1 z|} ≤ p := by
  have hβ := scalarPlannerWeight_ge_one (k := fun _ => m) y A
  have hB := scalarPlannerWeight_le_calibrationBound y (fun i j => (hy i j).1) hc A
  have hR := calibrationPlannerLevel_error (zero_le_one.trans hβ) hB hh
  have hQuery := scalarPlannerBankQuery_correct (calibrationPlannerLevel m h) h p
    (exists_confidence_level hp.1 hp.2) hh hp y hy (A,(u,z)) hR
  rwa [scalarPlannerValue_eq_continuation y _ A hu hz, planner_empirical_eq] at hQuery

noncomputable def calibrationTargetCall (h p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    TargetEstimator n m (CalibrationPlannerSeed n m h p hp) :=
  fun y z s => calibrationPlannerCall h p hp y Finset.univ 1 z s

omit [NeZero m] in
theorem measurable_calibrationTargetCall (h p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun q : Reservoir n m × (ℝ × CalibrationPlannerSeed n m h p hp) =>
      calibrationTargetCall h p hp q.1 q.2.1 q.2.2) := by
  let Ω := Reservoir n m × (ℝ × CalibrationPlannerSeed n m h p hp)
  let X := Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × CalibrationPlannerSeed n m h p hp)))
  let f : X → ℝ := fun q => calibrationPlannerCall h p hp q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  let g : Ω → X := fun q => (q.1,(Finset.univ,(1,q.2)))
  change Measurable (f ∘ g)
  have hf : Measurable f := measurable_calibrationPlannerCall (n := n) (m := m) h p hp
  have h₀ : Measurable (fun q : Ω => q.1) := measurable_fst
  have h₁ : Measurable (fun q : Ω => q.2) := measurable_snd
  have hg : Measurable g := h₀.prodMk (measurable_const.prodMk (measurable_const.prodMk h₁))
  exact hf.comp hg

theorem calibrationTargetCall_correct_ae (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    (mu : ℝ) (hh : 1/(m : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hp : 1/((m : ℝ)^2*(4*(m : ℝ)+1)) ∈ Ioo (0 : ℝ) 1) :
    let h := 1/(m : ℝ)
    let p := 1/((m : ℝ)^2*(4*(m : ℝ)+1))
    ∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
      (calibrationPlannerSeedLaw n m h p hp).real {s | h < |calibrationTargetCall h p hp
        (reservoirCoordinates.symm a) (targetGrid j) s -
        optimalScalarValue (trainingInstance a) 1 (targetGrid j)|} ≤ p := by
  dsimp only
  have hUnit : ∀ᵐ a ∂P.trainingCoordinateLaw m, ∀ q, a q ∈ Icc (0 : ℝ) 1 := by
    apply ae_all_iff.mpr
    intro q
    have h := measurePreserving_eval (fun q : Fin n × Fin m => P.law q.1) q
    filter_upwards [h.quasiMeasurePreserving.ae (P.nonnegative q.1),
      h.quasiMeasurePreserving.ae (hcap q.1)] with a ha0 ha1
    exact ⟨ha0,ha1⟩
  filter_upwards [hUnit] with a ha he j
  let Q := trainingInstance a
  let y := reservoirCoordinates.symm a
  have hy (i : Fin n) (l : Fin m) : y i l ∈ Icc (0 : ℝ) 1 := ha (i,l)
  have hc : Q.positiveCount ≤ targetCountCutoff m := (empiricalPositiveCount_eq a).symm.trans_le he.1
  have hz : targetGrid j ∈ Icc (0 : ℝ) 4 := by
    refine ⟨targetGrid_nonnegative j, ?_⟩
    have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
    apply (div_le_iff₀ hm).mpr
    exact_mod_cast (show j.val ≤ 4*m by have hj := j.isLt; omega)
  have hv : Q.continuationValue Finset.univ 1 1 (targetGrid j) =
      optimalScalarValue Q 1 (targetGrid j) := by
    rw [Instance.continuationValue, mul_one]
    exact (Q.optimalScalarValue_eq_restrictTo_of_zero_outside Finset.univ
      (totalEmpiricalInstance_integrable y) (by simp) zero_le_one hz.1).symm
  have ht := calibrationPlannerCall_correct _ _ hh hp y hy hc Finset.univ 1 (targetGrid j)
    ⟨zero_le_one, le_rfl⟩ hz
  change (calibrationPlannerSeedLaw _ _ _ _ hp).real {s | 1/(m : ℝ) <
    |calibrationTargetCall _ _ hp y (targetGrid j) s - optimalScalarValue Q 1 (targetGrid j)|} ≤ _
  rw [← hv]
  exact ht

end ProphetSecretary.Statistics.Calibration
