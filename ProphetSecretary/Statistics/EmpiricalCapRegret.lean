import ProphetSecretary.Statistics.EmpiricalScalarOptimization
import ProphetSecretary.Statistics.EmpiricalCapAcceptanceAE

/-!
# Regret of the empirical policy with cap acceptance

Equation `eq:bayes-empirical-loss` follows by adding the actual empirical
optimization regret and the uniform cost of accepting caps and rejecting
zero. The selected scalar may depend on all training samples and any
independent auxiliary randomness. The constant is fixed before the instance.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model

noncomputable def empiricalCapRegretConstant (lo : ℝ) : ℝ :=
  empiricalCandidateRegretConstant lo (1/4)+100/361

lemma empiricalCapRegretConstant_positive {lo : ℝ} (hlo : 0<lo) (hlohi : lo≤1/4) :
    0<empiricalCapRegretConstant lo := by
  have h := empiricalCandidateRegretConstant_positive hlo hlohi
  unfold empiricalCapRegretConstant
  linarith

theorem Learner.empiricalCapAcceptance_expected_regret_le {n k : ℕ} [NeZero k]
    (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z) {lo : ℝ}
    (hlo : 0<lo) (hlohi : lo≤1/4) (hRange : ∀ p, Z p∈Icc lo (1/4 : ℝ))
    (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80) :
    (∫ p, optimalScalarValue P 1 (Z p)-
      ((Learner.empiricalCapAcceptance Seed ν Z hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
      ∂(P.reservoirLaw k).prod ν) ≤
        empiricalCapRegretConstant lo*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(k : ℝ) := by
  let K := Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ
  let L := Learner.empiricalCapAcceptance Seed ν Z hZ
  let D := (P.reservoirLaw k).prod ν
  let gapK := fun p : Reservoir n k × Seed => optimalScalarValue P 1 (Z p)-
    (K.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
  let gapL := fun p : Reservoir n k × Seed => optimalScalarValue P 1 (Z p)-
    (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
  let loss := fun p : Reservoir n k × Seed => (K.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)-
    (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
  have hP := P.integrable_maximum_of_bounded hcap
  have hz (p) : 0≤Z p := hlo.le.trans (hRange p).1
  have hUpper : ∀ᵐ p ∂D, Z p≤1/4 := Eventually.of_forall (fun p => (hRange p).2)
  have hK : Integrable gapK D := K.integrable_selectedRegret P hP hZ hz hUpper
  have hL : Integrable gapL D := L.integrable_selectedRegret P hP hZ hz hUpper
  have hLoss : Integrable loss D := by
    apply (hL.sub hK).congr
    filter_upwards [] with p
    change (gapL p-gapK p)=loss p
    dsimp only [gapL,gapK,loss]
    ring
  have hSplit : (∫ p, gapL p ∂D)=(∫ p, gapK p ∂D)+∫ p, loss p ∂D := by
    rw [← integral_add hK hLoss]
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by dsimp only [gapL,gapK,loss,Pi.add_apply]; ring)
  have hEmp := Learner.empiricalSelectedScalar_expected_regret_le P hcap ν hZ hlo hlohi hRange
  have hMod := Learner.empiricalCapAcceptance_expected_loss_le_const Seed ν Z hZ hlo
    (fun p => (hRange p).1) (fun p => (hRange p).2) P hcap hM
  change (∫ p, gapL p ∂D)≤_
  rw [hSplit]
  apply (add_le_add hEmp hMod).trans
  have hk : (0 : ℝ)<k := Nat.cast_pos.mpr (NeZero.pos k)
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ hk.le
  unfold empiricalCapRegretConstant
  have hConst := empiricalCandidateRegretConstant_positive hlo hlohi
  have hS : 0≤P.totalFirstMoment := Finset.sum_nonneg (fun i _ => integral_nonneg_of_ae (P.nonnegative i))
  nlinarith only [hConst,hS]

theorem Learner.empiricalCapAcceptance_expected_regret_le_ae {n k : ℕ} [NeZero k]
    (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z) {lo : ℝ}
    (hlo : 0<lo) (hlohi : lo≤1/4) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80)
    (hRange : ∀ᵐ p ∂(P.reservoirLaw k).prod ν, Z p∈Icc lo (1/4 : ℝ)) :
    ∃ hT : Measurable (capAcceptanceScalar lo Z),
      (∫ p, optimalScalarValue P 1 (Z p)-
        ((Learner.empiricalCapAcceptance Seed ν (capAcceptanceScalar lo Z) hT).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
        ∂(P.reservoirLaw k).prod ν) ≤
          empiricalCapRegretConstant lo*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(k : ℝ) := by
  let T := capAcceptanceScalar lo Z
  have hT : Measurable T := measurable_const.max (measurable_const.min hZ)
  have hTrange (p) : T p∈Icc lo (1/4 : ℝ) :=
    ⟨le_max_left _ _,max_le hlohi (min_le_left _ _)⟩
  have hEq : Z=ᵐ[(P.reservoirLaw k).prod ν] T := by
    filter_upwards [hRange] with p hp
    dsimp only [T,capAcceptanceScalar]
    rw [min_eq_right hp.2,max_eq_right hp.1]
  refine ⟨hT,?_⟩
  apply le_trans _ (Learner.empiricalCapAcceptance_expected_regret_le Seed ν T hT hlo hlohi hTrange P hcap hM)
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [hEq] with p hp
  rw [hp]

end ProphetSecretary.Model
