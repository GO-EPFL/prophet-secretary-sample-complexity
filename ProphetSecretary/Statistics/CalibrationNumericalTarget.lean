import ProphetSecretary.Model.ScalarRatio
import ProphetSecretary.Model.TwoOfferCompetitiveBound
import ProphetSecretary.Model.EmpiricalMomentsMeasurability
import ProphetSecretary.Model.TrainingCoordinates
import ProphetSecretary.Model.EmpiricalValueMeasurability
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The finite numerical duration target

The target uses one empirical product, a finite duration-coefficient grid,
and returned continuation estimates. Its guards and clipping are defined on
every raw training outcome. No unknown-law quantity or competitive constant
is an input to this rule. Paper: `eq:calibration-numerical-target`.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m : ℕ} [NeZero m]

abbrev TargetGrid (m : ℕ) := Fin (4*m+1)

/-- The duration-coefficient mesh used by the target queries. -/
noncomputable def targetGrid (j : TargetGrid m) : ℝ := (j.val : ℝ)/(m : ℝ)

omit [NeZero m] in
lemma targetGrid_nonnegative (j : TargetGrid m) : 0 ≤ targetGrid j := by
  dsimp [targetGrid]
  positivity

/-- The empirical positive count, computed by counting the positive observations. -/
noncomputable def empiricalPositiveCount (y : (Fin n × Fin m) → ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ q, if 0 < y q then (1 : ℝ) else 0

omit [NeZero m] in
lemma measurable_empiricalPositiveCount : Measurable (@empiricalPositiveCount n m) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro q _
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply q))
    measurable_const measurable_const

/-- Integer upper logarithm realizes the paper's count cutoff. -/
noncomputable def targetCountCutoff (m : ℕ) : ℝ := 4*(Nat.clog 2 m : ℝ)+2

/-- The product empirical law supplied by the first block. -/
noncomputable def trainingInstance (y : (Fin n × Fin m) → ℝ) : Instance n :=
  totalEmpiricalInstance (reservoirCoordinates.symm y)

lemma empiricalPositiveCount_eq (y : (Fin n × Fin m) → ℝ) :
    empiricalPositiveCount y = (trainingInstance y).positiveCount := by
  have he (i : Fin n) : ((trainingInstance y).law i).real (Ioi 0) =
      (m : ℝ)⁻¹ * ∑ j : Fin m, if 0 < y (i,j) then (1 : ℝ) else 0 := by
    have hI := integral_indicator_one (μ := (trainingInstance y).law i) (s := Ioi (0 : ℝ)) measurableSet_Ioi
    rw [← hI]
    change (∫ x, if 0 < x then (1 : ℝ) else 0 ∂(totalEmpiricalInstance (reservoirCoordinates.symm y)).law i) = _
    rw [totalEmpiricalInstance_integral]
    apply congrArg ((m : ℝ)⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro j _
    simp [reservoirCoordinates]
  symm
  change (∑ i, ((trainingInstance y).law i).real (Ioi 0)) = _
  simp_rw [he]
  rw [← Finset.mul_sum]
  unfold empiricalPositiveCount
  rw [Fintype.sum_prod_type]

/-- The maximum benchmark of the product empirical distribution. -/
noncomputable def trainingExpectedMaximum (y : (Fin n × Fin m) → ℝ) : ℝ :=
  (trainingInstance y).expectedMaximum

lemma measurable_trainingExpectedMaximum : Measurable (@trainingExpectedMaximum n m _) :=
  measurable_totalEmpirical_expectedMaximum (fun i j => by fun_prop)

/-- The finite ratio minimum before clipping. -/
noncomputable def targetMinimumRatio (y : (Fin n × Fin m) → ℝ)
    (v : TargetGrid m → ℝ) : ℝ :=
  Finset.univ.inf' (by exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
    (fun j => (v j+1/(m : ℝ))/(trainingExpectedMaximum y+targetGrid j))

/-- The actual guarded finite target; `v` is the array of planner outputs. -/
noncomputable def numericalTarget (mu : ℝ) (y : (Fin n × Fin m) → ℝ)
    (v : TargetGrid m → ℝ) : ℝ :=
  if targetCountCutoff m < empiricalPositiveCount y ∨ trainingExpectedMaximum y < mu/2 then
    4/5
  else min (4/5) (max (1/2) (targetMinimumRatio y v))

lemma numericalTarget_range (mu : ℝ) (y : (Fin n × Fin m) → ℝ) (v : TargetGrid m → ℝ) :
    numericalTarget mu y v ∈ Icc (1/2 : ℝ) (4/5) := by
  unfold numericalTarget
  split_ifs
  · norm_num
  · exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma measurable_targetMinimumRatio :
    Measurable (fun p : (((Fin n × Fin m) → ℝ) × (TargetGrid m → ℝ)) =>
      targetMinimumRatio p.1 p.2) := by
  have hm : Measurable ((Finset.univ : Finset (TargetGrid m)).inf'
      (by exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
      (fun j => fun p : (((Fin n × Fin m) → ℝ) × (TargetGrid m → ℝ)) =>
        (p.2 j+1/(m : ℝ))/(trainingExpectedMaximum p.1+targetGrid j))) := by
    apply Finset.inf'_induction
    · intro f hf g hg
      exact hf.inf hg
    · intro j _
      exact (((measurable_pi_apply j).comp measurable_snd).add_const _).div
        ((measurable_trainingExpectedMaximum.comp measurable_fst).add_const _)
  convert hm using 1
  funext p
  simp only [targetMinimumRatio, Finset.inf'_apply]

lemma measurable_numericalTarget (mu : ℝ) :
    Measurable (fun p : (((Fin n × Fin m) → ℝ) × (TargetGrid m → ℝ)) =>
      numericalTarget mu p.1 p.2) := by
  unfold numericalTarget
  apply Measurable.ite
    ((measurableSet_lt measurable_const (measurable_empiricalPositiveCount.comp measurable_fst)).union
      (measurableSet_lt (measurable_trainingExpectedMaximum.comp measurable_fst) measurable_const))
    measurable_const
  exact measurable_const.min (measurable_const.max measurable_targetMinimumRatio)

/-- Accurate lower bounds on all queried values preserve the competitive lower target. -/
lemma numericalTarget_ge_competitiveRatio (mu : ℝ) (hmu : 0 < mu)
    (y : (Fin n × Fin m) → ℝ) (v : TargetGrid m → ℝ)
    (hSafe : ∀ j, optimalScalarValue (trainingInstance y) 1 (targetGrid j) ≤ v j+1/(m : ℝ)) :
    optimalCompetitiveRatio ≤ numericalTarget mu y v := by
  have hC : optimalCompetitiveRatio ≤ (4/5 : ℝ) := by
    linarith [optimalCompetitiveRatio_le_threeQuarters]
  unfold numericalTarget
  split_ifs with hg
  · exact hC
  · have hM : 0 < trainingExpectedMaximum y := by
      have hguard : mu/2 ≤ trainingExpectedMaximum y := le_of_not_gt (fun h => hg (Or.inr h))
      linarith
    have hP : (trainingInstance y).HasPositiveFiniteMaximum :=
      ⟨totalEmpiricalInstance_integrable (reservoirCoordinates.symm y), hM⟩
    have hmin : optimalCompetitiveRatio ≤ targetMinimumRatio y v := by
      apply Finset.le_inf'
      intro j _
      have hz := targetGrid_nonnegative j
      have hRatio := ((trainingInstance y).optimalScalarRatio_bounds hP).1.trans
        ((trainingInstance y).optimalScalarRatio_le_durationScalarRatio hP hz)
      have hd : 0 < trainingExpectedMaximum y+targetGrid j := add_pos_of_pos_of_nonneg hM hz
      exact hRatio.trans (div_le_div_of_nonneg_right (hSafe j) hd.le)
    exact le_min hC (hmin.trans (le_max_right _ _))

/-- A deterministic lower grid neighbor loses at most one mesh interval. -/
lemma exists_targetGrid_lower_neighbor {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 4) :
    ∃ j : TargetGrid m, targetGrid j ≤ z ∧ z-targetGrid j ≤ 1/(m : ℝ) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  let k := ⌊(m : ℝ)*z⌋₊
  have hk0 : (k : ℝ) ≤ (m : ℝ)*z := Nat.floor_le (mul_nonneg hm.le hz.1)
  have hk1 : (m : ℝ)*z < (k : ℝ)+1 := Nat.lt_floor_add_one ((m : ℝ)*z)
  have hk : k < 4*m+1 := by
    have hbound := mul_le_mul_of_nonneg_left hz.2 hm.le
    have hcast : (k : ℝ) < ((4*m+1 : ℕ) : ℝ) := by push_cast; nlinarith
    exact_mod_cast hcast
  let j : TargetGrid m := ⟨k, hk⟩
  have he : targetGrid j*(m : ℝ) = k := by dsimp [targetGrid, j]; field_simp [hm.ne']
  have hj : targetGrid j ≤ z := by
    apply (div_le_iff₀ hm).mpr
    simpa only [mul_comm] using hk0
  refine ⟨j, hj, ?_⟩
  apply (le_div_iff₀ hm).mpr
  nlinarith

private lemma valueRatio_lower_neighbor {M z s V W : ℝ}
    (hM : 0 < M) (hs : 0 ≤ s) (hsz : s ≤ z)
    (hVW : V ≤ W) (hW : W ≤ M+z) :
    V/(M+s) ≤ W/(M+z)+(z-s)/M := by
  have hDs : 0 < M+s := add_pos_of_pos_of_nonneg hM hs
  have hDz : 0 < M+z := add_pos_of_pos_of_nonneg hM (hs.trans hsz)
  have hDsm : M ≤ M+s := by linarith
  have hZ : 0 ≤ z-s := sub_nonneg.mpr hsz
  have hA : W/(M+s) ≤ W/(M+z)+(z-s)/(M+s) := by
    apply (div_le_iff₀ hDs).mpr
    have he : (W/(M+z)+(z-s)/(M+s))*(M+s)-W =
        ((M+z)-W)*(z-s)/(M+z) := by
      field_simp [hDs.ne', hDz.ne']
      ring
    have hNonneg : 0 ≤ ((M+z)-W)*(z-s)/(M+z) :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hW) hZ) hDz.le
    rw [← he] at hNonneg
    linarith
  have hB : (z-s)/(M+s) ≤ (z-s)/M := div_le_div_of_nonneg_left hZ hM hDsm
  exact (div_le_div_of_nonneg_right hVW hDs.le).trans
    (hA.trans (add_le_add le_rfl hB))

/-- A lower grid neighbor approximates the exact duration ratio from above. -/
lemma targetMinimumRatio_le_at (y : (Fin n × Fin m) → ℝ) (v : TargetGrid m → ℝ)
    (hM : 0 < trainingExpectedMaximum y) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 4)
    (hAcc : ∀ j, v j ≤ optimalScalarValue (trainingInstance y) 1 (targetGrid j)+1/(m : ℝ)) :
    targetMinimumRatio y v ≤ (trainingInstance y).durationScalarRatio z +
      3/((m : ℝ)*trainingExpectedMaximum y) := by
  obtain ⟨j, hle, hdist⟩ := exists_targetGrid_lower_neighbor (m := m) hz
  have hs := targetGrid_nonnegative j
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hDs : 0 < trainingExpectedMaximum y+targetGrid j := add_pos_of_pos_of_nonneg hM hs
  have hQ := totalEmpiricalInstance_integrable (reservoirCoordinates.symm y)
  have hVW := optimalScalarValue_mono (trainingInstance y) hQ zero_le_one hs le_rfl hle
  have hW := optimalScalarValue_le_benchmark (trainingInstance y) hQ zero_le_one hz.1
  have hRatio := valueRatio_lower_neighbor hM hs hle hVW (by simpa only [one_mul, trainingExpectedMaximum] using hW)
  have hFirst : targetMinimumRatio y v ≤
      (v j+1/(m : ℝ))/(trainingExpectedMaximum y+targetGrid j) :=
    Finset.inf'_le _ (Finset.mem_univ j)
  have hEst : (v j+1/(m : ℝ))/(trainingExpectedMaximum y+targetGrid j) ≤
      optimalScalarValue (trainingInstance y) 1 (targetGrid j)/(trainingExpectedMaximum y+targetGrid j) +
        (2/(m : ℝ))/(trainingExpectedMaximum y+targetGrid j) := by
    rw [← add_div]
    have hn := add_le_add (hAcc j) (le_refl (1/(m : ℝ)))
    have hn' : v j+1/(m : ℝ) ≤ optimalScalarValue (trainingInstance y) 1 (targetGrid j)+2/(m : ℝ) :=
      hn.trans_eq (by ring)
    exact div_le_div_of_nonneg_right hn' hDs.le
  have hNum : 0 ≤ 2/(m : ℝ) := by positivity
  have hDen : trainingExpectedMaximum y ≤ trainingExpectedMaximum y+targetGrid j := by linarith
  have hPrec := div_le_div_of_nonneg_left hNum hM hDen
  have hMesh := div_le_div_of_nonneg_right hdist hM.le
  calc
    targetMinimumRatio y v ≤ _ := hFirst.trans hEst
    _ ≤ ((trainingInstance y).durationScalarRatio z+(z-targetGrid j)/trainingExpectedMaximum y) +
        (2/(m : ℝ))/trainingExpectedMaximum y :=
      add_le_add hRatio hPrec
    _ ≤ (trainingInstance y).durationScalarRatio z+(1/(m : ℝ))/trainingExpectedMaximum y+
        (2/(m : ℝ))/trainingExpectedMaximum y := by linarith
    _ = _ := by ring

/-- Only eligible training arrays invoke the numerical target queries. -/
def targetEligible (mu : ℝ) (y : (Fin n × Fin m) → ℝ) : Prop :=
  empiricalPositiveCount y ≤ targetCountCutoff m ∧ mu/2 ≤ trainingExpectedMaximum y

/-- Failure means an actually invoked target query misses its prescribed tolerance. -/
def queryFailure (mu : ℝ) (y : (Fin n × Fin m) → ℝ) (v : TargetGrid m → ℝ) : Prop :=
  targetEligible mu y ∧ ¬∀ j, |v j-optimalScalarValue (trainingInstance y) 1 (targetGrid j)| ≤ 1/(m : ℝ)

lemma measurableSet_queryFailure (mu : ℝ) :
    MeasurableSet {p : (((Fin n × Fin m) → ℝ) × (TargetGrid m → ℝ)) | queryFailure mu p.1 p.2} := by
  have he : MeasurableSet {p : (((Fin n × Fin m) → ℝ) × (TargetGrid m → ℝ)) | targetEligible mu p.1} :=
    (measurableSet_le (measurable_empiricalPositiveCount.comp measurable_fst) measurable_const).inter
      (measurableSet_le measurable_const (measurable_trainingExpectedMaximum.comp measurable_fst))
  have hAll : MeasurableSet {p : (((Fin n × Fin m) → ℝ) × (TargetGrid m → ℝ)) |
      ∀ j, |p.2 j-optimalScalarValue (trainingInstance p.1) 1 (targetGrid j)| ≤ 1/(m : ℝ)} := by
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    have hVal : Measurable (fun p : (((Fin n × Fin m) → ℝ) × (TargetGrid m → ℝ)) =>
        optimalScalarValue (trainingInstance p.1) 1 (targetGrid j)) :=
      measurable_optimalScalarValue_totalEmpirical (fun i l => by fun_prop)
        measurable_const measurable_const (fun _ => zero_lt_one) (fun _ => targetGrid_nonnegative j)
    exact measurableSet_le (((measurable_pi_apply j).comp measurable_snd).sub hVal).abs measurable_const
  exact he.inter hAll.compl

lemma numericalTarget_ge_competitiveRatio_of_no_failure (mu : ℝ) (hmu : 0 < mu)
    (y : (Fin n × Fin m) → ℝ) (v : TargetGrid m → ℝ) (hGood : ¬queryFailure mu y v) :
    optimalCompetitiveRatio ≤ numericalTarget mu y v := by
  by_cases hg : targetCountCutoff m < empiricalPositiveCount y ∨ trainingExpectedMaximum y < mu/2
  · simp only [numericalTarget, if_pos hg]
    linarith [optimalCompetitiveRatio_le_threeQuarters]
  · have hEligible : targetEligible mu y :=
      ⟨le_of_not_gt (fun h => hg (Or.inl h)), le_of_not_gt (fun h => hg (Or.inr h))⟩
    have hAcc : ∀ j, |v j-optimalScalarValue (trainingInstance y) 1 (targetGrid j)| ≤ 1/(m : ℝ) := by
      by_contra h
      exact hGood ⟨hEligible, h⟩
    apply numericalTarget_ge_competitiveRatio mu hmu y v
    intro j
    have h := (abs_le.mp (hAcc j)).1
    linarith

/-- The only possible expected downward loss is charged to actual failed queries. -/
theorem numericalTarget_expected_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (mu : ℝ) (hmu : 0 < mu)
    (y : Ω → (Fin n × Fin m) → ℝ) (v : Ω → TargetGrid m → ℝ)
    (hy : Measurable y) (hv : Measurable v) :
    optimalCompetitiveRatio-μ.real {ω | queryFailure mu (y ω) (v ω)} ≤
      ∫ ω, numericalTarget mu (y ω) (v ω) ∂μ := by
  let E : Set Ω := {ω | queryFailure mu (y ω) (v ω)}
  have hE : MeasurableSet E := (measurableSet_queryFailure mu).preimage (hy.prodMk hv)
  have hT : Integrable (fun ω => numericalTarget mu (y ω) (v ω)) μ := by
    apply Integrable.of_bound
      ((measurable_numericalTarget mu).comp (hy.prodMk hv)).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by
      change ‖numericalTarget mu (y ω) (v ω)‖ ≤ 1
      have hr := numericalTarget_range mu (y ω) (v ω)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hr.1])]
      linarith [hr.2]
  have hInd : Integrable (E.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hE
  have h := integral_mono ((integrable_const optimalCompetitiveRatio).sub hInd) hT (fun ω => by
    change optimalCompetitiveRatio-E.indicator (fun _ : Ω => (1 : ℝ)) ω ≤ numericalTarget mu (y ω) (v ω)
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      have hr := (numericalTarget_range mu (y ω) (v ω)).1
      linarith [optimalCompetitiveRatio_le_one]
    · rw [Set.indicator_of_notMem hω, sub_zero]
      exact numericalTarget_ge_competitiveRatio_of_no_failure mu hmu (y ω) (v ω) hω)
  change (∫ ω, optimalCompetitiveRatio-E.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) ≤
    (∫ ω, numericalTarget mu (y ω) (v ω) ∂μ) at h
  rw [integral_sub (integrable_const _) hInd, integral_const, probReal_univ, one_smul,
    integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one] at h
  exact h

end ProphetSecretary.Statistics.Calibration
