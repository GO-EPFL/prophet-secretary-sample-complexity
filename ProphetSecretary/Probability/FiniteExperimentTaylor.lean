import ProphetSecretary.Probability.NormalizedScoreResponse

/-!
# Uniform fixed-policy reward, duration and benchmark Taylor bounds

The same actual finite score family is used for all admissible policies, with
arbitrary independent auxiliary randomness. The constants 2HI and 2I depend
on the cap and information bound, not on the array dimension. Weights and
policy callbacks are fixed before perturbing the laws.
-/
open MeasureTheory Set
open scoped Classical Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability

theorem finite_likelihood_payoff_taylor
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H I : ℝ} (hH : 0≤H)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    let Q := fun m θ => (P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ
    ∀ m (π : RandomizedPolicy (sizes m)) θ, |θ|≤1/4 →
      |π.expectedReward (Q m θ)-π.expectedReward (P m)-θ*π.expectedRewardScore (P m) (score m)|≤2*H*θ^2*I ∧
      |π.expectedDuration (Q m θ)-π.expectedDuration (P m)-θ*π.expectedDurationScore (P m) (score m)|≤2*θ^2*I ∧
      |(Q m θ).expectedMaximum-(P m).expectedMaximum-θ*(P m).expectedMaximumScore (score m)|≤2*H*θ^2*I := by
  let Q := fun m θ => (P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ
  have hQ (m θ) (hθ : |θ|≤1/4) : Q m θ=(P m).likelihoodTilt (score m) (hh m) (hb m) (hm m) θ hθ := by
    change (P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ=_
    rw [(P m).likelihoodWidePath_eq_quarter (score m) (hh m) (hb m) (hm m) hθ,
      (P m).likelihoodPath_of_mem (score m) (hh m) (hb m) (hm m) hθ]
  dsimp only
  intro m π θ hθ
  have hR := π.expectedReward_likelihood_taylor (P m) hH (hCap m) (score m) (hh m) (hb m) (hm m) hθ
  have hT := π.expectedDuration_likelihood_taylor (P m) (score m) (hh m) (hb m) (hm m) hθ
  have hM := (P m).expectedMaximum_likelihood_taylor hH (hCap m) (score m) (hh m) (hb m) (hm m) hθ
  have hRS : (∫ ω : π.World, π.realizedReward ω*completeScore (score m) ω.1 ∂(P m).worldLaw π.seedLaw)=
      π.expectedRewardScore (P m) (score m) := integral_congr_ae (Filter.Eventually.of_forall (fun _ => mul_comm _ _))
  have hTS : (∫ ω : π.World, π.realizedDuration ω*completeScore (score m) ω.1 ∂(P m).worldLaw π.seedLaw)=
      π.expectedDurationScore (P m) (score m) := integral_congr_ae (Filter.Eventually.of_forall (fun _ => mul_comm _ _))
  have hMS : (∫ x, Instance.maximum x*completeScore (score m) x ∂(P m).valuesLaw)=
      (P m).expectedMaximumScore (score m) := integral_congr_ae (Filter.Eventually.of_forall (fun _ => mul_comm _ _))
  rw [hRS] at hR
  rw [hTS] at hT
  rw [hMS] at hM
  refine ⟨?_,?_,?_⟩
  · calc
      _ = |π.expectedReward ((P m).likelihoodTilt (score m) (hh m) (hb m) (hm m) θ hθ)-
          π.expectedReward (P m)-θ*π.expectedRewardScore (P m) (score m)| :=
        congrArg (fun r : ℝ => |r-π.expectedReward (P m)-θ*π.expectedRewardScore (P m) (score m)|)
          (congrArg (fun A : Instance (sizes m) => π.expectedReward A) (hQ m θ hθ))
      _ ≤ _ := hR.trans (mul_le_mul_of_nonneg_left (hInfo m) (by positivity))
  · calc
      _ = |π.expectedDuration ((P m).likelihoodTilt (score m) (hh m) (hb m) (hm m) θ hθ)-
          π.expectedDuration (P m)-θ*π.expectedDurationScore (P m) (score m)| :=
        congrArg (fun r : ℝ => |r-π.expectedDuration (P m)-θ*π.expectedDurationScore (P m) (score m)|)
          (congrArg (fun A : Instance (sizes m) => π.expectedDuration A) (hQ m θ hθ))
      _ ≤ _ := hT.trans (mul_le_mul_of_nonneg_left (hInfo m) (by positivity))
  · calc
      _ = |((P m).likelihoodTilt (score m) (hh m) (hb m) (hm m) θ hθ).expectedMaximum-
          (P m).expectedMaximum-θ*(P m).expectedMaximumScore (score m)| :=
        congrArg (fun r : ℝ => |r-(P m).expectedMaximum-θ*(P m).expectedMaximumScore (score m)|)
          (congrArg (fun A : Instance (sizes m) => A.expectedMaximum) (hQ m θ hθ))
      _ ≤ _ := hM.trans (mul_le_mul_of_nonneg_left (hInfo m) (by positivity))
end ProphetSecretary.Model
