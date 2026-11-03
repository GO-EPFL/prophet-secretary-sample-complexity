import ProphetSecretary.Statistics.CalibratedScalarCalls
import ProphetSecretary.Statistics.ScalarPlannerFairQuery
import ProphetSecretary.Statistics.PlannerBitPrecision

/-!
# Fair-bit scalar calls for the calibrated learner

All levels in a query use the same public dyadic precision. A level is
selected from the observed empirical rows before the query reads its
independent fair-bit block.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m : ℕ}

abbrev CalibrationFairSeed (n m b : ℕ) (h p : ℝ) (hp : p∈Ioo (0 : ℝ) 1) :=
  (j : Fin (calibrationPlannerLevel m (h/2)+1)) →
    Fin (confidenceCopyCount p (exists_confidence_level hp.1 hp.2)) →
      MultilevelTree (PlannerFairSeed n b) j.val

noncomputable def calibrationFairSeedLaw (n m b : ℕ) (h p : ℝ) (hp : p∈Ioo (0 : ℝ) 1) :
    Measure (CalibrationFairSeed n m b h p hp) :=
  Measure.pi fun j => Measure.pi fun _ => multilevelTreeLaw (plannerFairSeedLaw n b) j.val

instance (n m b : ℕ) (h p : ℝ) (hp : p∈Ioo (0 : ℝ) 1) :
    IsProbabilityMeasure (calibrationFairSeedLaw n m b h p hp) := by
  unfold calibrationFairSeedLaw
  infer_instance

noncomputable def decodeCalibrationFairSeed (b : ℕ) (h p : ℝ) (hp : p∈Ioo (0 : ℝ) 1)
    (s : CalibrationFairSeed n m b h p hp) : CalibrationPlannerSeed n m (h/2) p hp :=
  fun j c => multilevelTreeMap (plannerFairSeedReal b) j.val (s j c)

lemma measurable_decodeCalibrationFairSeed (b : ℕ) (h p : ℝ) (hp : p∈Ioo (0 : ℝ) 1) :
    Measurable (decodeCalibrationFairSeed (n := n) (m := m) b h p hp) := by
  apply measurable_pi_lambda
  intro j
  apply measurable_pi_lambda
  intro c
  exact (measurePreserving_multilevelTreeMap (measurePreserving_plannerFairSeedReal n b) j.val).measurable.comp
    ((measurable_pi_apply c).comp (measurable_pi_apply j))

noncomputable def calibrationFairCall (b : ℕ) (h p : ℝ) (hp : p∈Ioo (0 : ℝ) 1) :
    ContinuationEstimator n m (CalibrationFairSeed n m b h p hp) :=
  fun y A u z s => calibrationPlannerCall (h/2) p hp y A u z (decodeCalibrationFairSeed b h p hp s)

set_option maxHeartbeats 800000 in
theorem measurable_calibrationFairCall (b : ℕ) (h p : ℝ) (hp : p∈Ioo (0 : ℝ) 1) :
    Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × CalibrationFairSeed n m b h p hp))) =>
      calibrationFairCall b h p hp q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  let Ω := Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × CalibrationFairSeed n m b h p hp)))
  let X := Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × CalibrationPlannerSeed n m (h/2) p hp)))
  let f : X → ℝ := fun q => calibrationPlannerCall (h/2) p hp q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  let g : Ω → X := fun q => (q.1,(q.2.1,(q.2.2.1,(q.2.2.2.1,decodeCalibrationFairSeed b h p hp q.2.2.2.2))))
  change Measurable (f ∘ g)
  have hf : Measurable f := measurable_calibrationPlannerCall (n := n) (m := m) (h/2) p hp
  have hs : Measurable (fun q : Ω => q.2.2.2.2) := by fun_prop
  have hd : Measurable (fun q : Ω => decodeCalibrationFairSeed b h p hp q.2.2.2.2) :=
    (measurable_decodeCalibrationFairSeed (n := n) (m := m) b h p hp).comp hs
  have hg : Measurable g := by
    dsimp only [g]
    fun_prop (disch := assumption)
  exact hf.comp hg

variable [NeZero m]

noncomputable def calibrationFairPrecision (n m : ℕ) [NeZero m] (h : ℝ) (hh : h∈Ioo (0 : ℝ) 1) : ℕ :=
  (countedPlannerBitPrecision n (calibrationWeightBound m) h
    (exists_confidence_level
      (plannerGridTolerance_pos n (zero_lt_one.trans_le (calibrationWeightBound_ge_one (m := m))) hh.1)
      (plannerGridTolerance_lt_one n (calibrationWeightBound_ge_one (m := m)) hh.2.le))).1

lemma calibrationFairPrecision_error (h : ℝ) (hh : h∈Ioo (0 : ℝ) 1)
    {β : ℝ} (hβ : β ≤ calibrationWeightBound m) :
    β*((10*(n : ℝ)+4)/(3*((2^calibrationFairPrecision n m h hh : ℕ) : ℝ))) ≤ h/4 := by
  have hG : calibrationWeightBound m *
      ((10*(n : ℝ)+4)/(3*((2^calibrationFairPrecision n m h hh : ℕ) : ℝ))) ≤ h/4 :=
    (countedPlannerBitPrecision_correct n (calibrationWeightBound_ge_one (m := m)) hh.1 hh.2.le _).2.1
  exact (mul_le_mul_of_nonneg_right hβ (by positivity)).trans hG

theorem calibrationFairCall_correct (h p : ℝ) (hh : h∈Ioo (0 : ℝ) 1)
    (hp : p∈Ioo (0 : ℝ) 1) (y : Reservoir n m) (hy : ∀ i j, y i j∈Icc (0 : ℝ) 1)
    (hc : (totalEmpiricalInstance y).positiveCount≤targetCountCutoff m)
    (A : Finset (Fin n)) (u z : ℝ) (hu : u∈Icc (0 : ℝ) 1) (hz : z∈Icc (0 : ℝ) 4) :
    let b := calibrationFairPrecision n m h hh
    (calibrationFairSeedLaw n m b h p hp).real {s |
      h < |calibrationFairCall b h p hp y A u z s-(totalEmpiricalInstance y).continuationValue A u 1 z|} ≤ p := by
  dsimp only
  let b := calibrationFairPrecision n m h hh
  let x : ScalarPlannerState n := (A,(u,z))
  let H := exists_confidence_level hp.1 hp.2
  let R := calibrationPlannerLevel m (h/2)
  let j := boundedScalarPlannerLevel (k := fun _ => m) R (h/2) y A
  let β := scalarPlannerWeight (k := fun _ => m) y A
  have hβ := scalarPlannerWeight_ge_one (k := fun _ => m) y A
  have hB := scalarPlannerWeight_le_calibrationBound y (fun i l => (hy i l).1) hc A
  have hh' : h/2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have hR := calibrationPlannerLevel_error (zero_le_one.trans hβ) hB hh'
  have hj : j.val = scalarPlannerLevel β (h/2) :=
    min_eq_right (scalarPlannerLevel_le_of_error hβ hh' hR)
  have hprec : 25*β^2*(1/2 : ℝ)^j.val ≤ (h/2)^2/64 := by
    rw [hj]
    exact scalarPlannerLevel_error hβ hh'
  have hGrid := calibrationFairPrecision_error (n := n) h hh hB
  have hQ := scalarPlannerFairQuery_correct y (fun i l => (hy i l).1) (fun i l => (hy i l).2)
    b x j.val h p hh.1 hp.1 hp.2 H hprec hGrid
  let v := (totalEmpiricalInstance y).continuationValue A u 1 z
  have hv : scalarPlannerValue y (fun i l => (hy i l).1) x = v := by
    rw [scalarPlannerValue_eq_continuation y _ A hu hz, planner_empirical_eq]
  have hAbs := continuous_abs.measurable.comp (hQ.1.sub_const v)
  let E := {s | h < |(scalarPlannerFairQuery y b x j.val p H s).value-v|}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hAbs
  have hLaw := measurePreserving_eval
    (fun l : Fin (R+1) => Measure.pi (fun _ : Fin (confidenceCopyCount p H) =>
      multilevelTreeLaw (plannerFairSeedLaw n b) l.val)) j
  unfold calibrationFairCall calibrationPlannerCall scalarPlannerBankQuery
  dsimp only
  rw [scalarPlannerClampRows_eq y hy]
  change (calibrationFairSeedLaw n m b h p hp).real ((fun s => s j) ⁻¹' E) ≤ p
  rw [← map_measureReal_apply hLaw.measurable hE,
    show (calibrationFairSeedLaw n m b h p hp).map (fun s => s j) = _ from hLaw.map_eq]
  have hResult := hQ.2.1
  rw [hv] at hResult
  exact hResult

noncomputable def calibrationFairTarget (b : ℕ) (h p : ℝ) (hp : p∈Ioo (0 : ℝ) 1) :
    TargetEstimator n m (CalibrationFairSeed n m b h p hp) :=
  fun y z s => calibrationFairCall b h p hp y Finset.univ 1 z s

omit [NeZero m] in
theorem measurable_calibrationFairTarget (b : ℕ) (h p : ℝ) (hp : p∈Ioo (0 : ℝ) 1) :
    Measurable (fun q : Reservoir n m × (ℝ × CalibrationFairSeed n m b h p hp) =>
      calibrationFairTarget b h p hp q.1 q.2.1 q.2.2) := by
  let Ω := Reservoir n m × (ℝ × CalibrationFairSeed n m b h p hp)
  let X := Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × CalibrationFairSeed n m b h p hp)))
  let f : X → ℝ := fun q => calibrationFairCall b h p hp q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  let g : Ω → X := fun q => (q.1,(Finset.univ,(1,q.2)))
  change Measurable (f ∘ g)
  have hf : Measurable f := measurable_calibrationFairCall b h p hp
  have hg : Measurable g := by
    have h₀ : Measurable (fun q : Ω => q.1) := measurable_fst
    have h₁ : Measurable (fun q : Ω => q.2) := measurable_snd
    exact h₀.prodMk (measurable_const.prodMk (measurable_const.prodMk h₁))
  exact hf.comp hg

theorem calibrationFairTarget_correct_ae (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    (mu : ℝ) (hh : 1/(m : ℝ)∈Ioo (0 : ℝ) 1)
    (hp : 1/((m : ℝ)^2*(4*(m : ℝ)+1))∈Ioo (0 : ℝ) 1) :
    let h := 1/(m : ℝ)
    let p := 1/((m : ℝ)^2*(4*(m : ℝ)+1))
    let b := calibrationFairPrecision n m h hh
    ∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
      (calibrationFairSeedLaw n m b h p hp).real {s | h < |calibrationFairTarget b h p hp
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
  have hy (i : Fin n) (l : Fin m) : y i l∈Icc (0 : ℝ) 1 := ha (i,l)
  have hc : Q.positiveCount≤targetCountCutoff m := (empiricalPositiveCount_eq a).symm.trans_le he.1
  have hz : targetGrid j∈Icc (0 : ℝ) 4 := by
    refine ⟨targetGrid_nonnegative j, ?_⟩
    have hm : (0 : ℝ)<m := by exact_mod_cast NeZero.pos m
    apply (div_le_iff₀ hm).mpr
    exact_mod_cast (show j.val ≤ 4*m by have hj := j.isLt; omega)
  have hv : Q.continuationValue Finset.univ 1 1 (targetGrid j) =
      optimalScalarValue Q 1 (targetGrid j) := by
    rw [Instance.continuationValue, mul_one]
    exact (Q.optimalScalarValue_eq_restrictTo_of_zero_outside Finset.univ
      (totalEmpiricalInstance_integrable y) (by simp) zero_le_one hz.1).symm
  have ht := calibrationFairCall_correct _ _ hh hp y hy hc Finset.univ 1 (targetGrid j)
    ⟨zero_le_one, le_rfl⟩ hz
  change (calibrationFairSeedLaw _ _ _ _ _ hp).real {s | 1/(m : ℝ) <
    |calibrationFairTarget _ _ _ hp y (targetGrid j) s - optimalScalarValue Q 1 (targetGrid j)|} ≤ _
  rw [← hv]
  exact ht

end ProphetSecretary.Statistics.Calibration
