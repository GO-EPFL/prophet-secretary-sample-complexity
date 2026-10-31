import ProphetSecretary.Statistics.FinitePriorExpectation
import ProphetSecretary.Statistics.PrefixLearnerIntegrability
import ProphetSecretary.Statistics.FinitePriorTargetScore
import ProphetSecretary.Statistics.FiniteResponseGame

/-!
# The true-target score and the implemented prefix learner

The hidden target selects reward or duration only in this analytical
expectation. The policy receives its visible training prefix. Reach is
compared with duration separately, under its proved monotonicity hypothesis.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n k : ℕ}

noncomputable def Learner.targetDurationPayoff (L : Learner n k) (P : Instance n)
    (J : Option (Fin n)) (C : ℝ) : ℝ :=
  match J with
  | none => L.expectedReward P-C*P.expectedMaximum
  | some _ => L.meanDuration P-C

lemma Learner.targetDurationPayoff_le_game (L : Learner n k) (P : Instance n) (J : Option (Fin n)) (C : ℝ)
    (hReach : ∀ i, L.meanDuration P≤L.reachProbability P i) :
    L.targetDurationPayoff P J C≤L.targetGamePayoff P J C := by
  cases J with
  | none => exact le_rfl
  | some i => exact sub_le_sub_right (hReach i) C

end ProphetSecretary.Model
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ} {Seed : Type} [MeasurableSpace Seed]

lemma prefixVisibleArray_eq_observe (F : FinitePrior n) (N b k : ℕ) (ω : BaseWorld F N) :
    prefixVisibleArray n N b k ω.2=F.observe N b k ω := by
  have hReservoir : reservoirCoordinates.symm
      (prefixOnlineValues n N (trainingLength N b k) (trainingLength_le N b k) ω.2).1=
        F.observedTraining N b k ω := by
    rw [F.observedTraining_eq]
    rfl
  unfold prefixVisibleArray
  rw [hReservoir,F.extend_observedTraining_eq]

lemma integral_onlineGameScore_atom (F : FinitePrior n) (N b k : ℕ) (θ : Fin F.size)
    (hP : Integrable Instance.maximum (F.offerInstance θ).valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable) (C : ℝ) :
    (∫ z : ValueArray n N × ((Fin n → ℝ) × Seed),
      F.onlineGameScore N b k π C F.rewardIndicator ((θ,z.1),z.2)
      ∂((F.offerInstance θ).trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν)) =
      (prefixLearner N b k ν π hπ).targetDurationPayoff (F.offerInstance θ) (F.target θ) C := by
  let P := F.offerInstance θ
  let R := fun z : ValueArray n N × ((Fin n → ℝ) × Seed) =>
    π.reward (prefixVisibleArray n N b k z.1,z.2.2) Finset.univ (fun i => z.1 (i,Fin.last N)) z.2.1
  let T := fun z : ValueArray n N × ((Fin n → ℝ) × Seed) =>
    π.stoppingTime (prefixVisibleArray n N b k z.1,z.2.2) Finset.univ (fun i => z.1 (i,Fin.last N)) z.2.1
  let X := fun z : ValueArray n N × ((Fin n → ℝ) × Seed) => Instance.maximum (fun i => z.1 (i,Fin.last N))
  have hR := integrable_prefixLearner_reward P hP N b k ν π hπ
  have hT := integrable_prefixLearner_duration P N b k ν π hπ
  have hX := integrable_onlineArray_maximum P hP N ((Instance.clocksLaw n).prod ν)
  cases hJ : F.target θ with
  | none =>
    have hFun : (fun z : ValueArray n N × ((Fin n → ℝ) × Seed) =>
        F.onlineGameScore N b k π C F.rewardIndicator ((θ,z.1),z.2))=(fun z => R z-C*X z) := by
      funext z
      rw [F.onlineGameScore_eq_mixture]
      have hQ : F.rewardIndicator (N:=N) (θ,z.1)=1 := by simp [rewardIndicator,hJ]
      rw [hQ]
      simp only [one_mul,sub_self,zero_mul,add_zero]
      change π.reward (F.observe N b k (θ,z.1),z.2.2) Finset.univ _ z.2.1-_ = _
      rw [←F.prefixVisibleArray_eq_observe N b k (θ,z.1)]
      rfl
    rw [hFun,integral_sub hR (hX.const_mul C),integral_const_mul]
    rw [integral_prefixLearner_reward P hP N b k ν π hπ,integral_onlineArray_maximum P N]
    rfl
  | some i =>
    have hFun : (fun z : ValueArray n N × ((Fin n → ℝ) × Seed) =>
        F.onlineGameScore N b k π C F.rewardIndicator ((θ,z.1),z.2))=(fun z => T z-C) := by
      funext z
      rw [F.onlineGameScore_eq_mixture]
      have hQ : F.rewardIndicator (N:=N) (θ,z.1)=0 := by simp [rewardIndicator,hJ]
      rw [hQ]
      simp only [zero_mul,sub_zero,one_mul,zero_add]
      change π.stoppingTime (F.observe N b k (θ,z.1),z.2.2) Finset.univ _ z.2.1-C = _
      rw [←F.prefixVisibleArray_eq_observe N b k (θ,z.1)]
      rfl
    rw [hFun,integral_sub hT (integrable_const C),integral_const,probReal_univ,one_smul]
    rw [integral_prefixLearner_duration P N b k ν π hπ]
    rfl

theorem integral_trueTargetScore_eq_average (F : FinitePrior n) (N b k : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable) {C : ℝ} (hC : C∈Icc (0 : ℝ) 1) :
    (∫ w, F.onlineGameScore N b k π C F.rewardIndicator w
      ∂F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν)) =
      ∑ θ : Fin F.size, (F.weight θ : ℝ)*
        (prefixLearner N b k ν π hπ).targetDurationPayoff (F.offerInstance θ) (F.target θ) C := by
  have hInt := F.onlineGameScore_integrable N b k hcap ν π hπ hC (F.measurable_rewardIndicator N)
    (Eventually.of_forall F.rewardIndicator_mem_unit)
  have hMeas : Measurable (F.onlineGameScore N b k π C F.rewardIndicator) :=
    (F.measurable_onlinePayoff N b k (measurable_gameBaseline N hπ C)).add
      (((F.measurable_rewardIndicator N).comp measurable_fst).mul
        (F.measurable_onlinePayoff N b k (measurable_gameFactor N hπ C)))
  rw [F.integral_auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν) hMeas hInt]
  apply Finset.sum_congr rfl
  intro θ _
  rw [F.integral_onlineGameScore_atom N b k θ ((F.offerInstance θ).integrable_maximum_of_bounded (hcap θ)) ν π hπ C]

end ProphetSecretary.Statistics.FinitePrior
