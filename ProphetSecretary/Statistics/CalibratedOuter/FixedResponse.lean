import ProphetSecretary.Statistics.OuterBoundedEligibility
import ProphetSecretary.Model.OuterNormalizedLift
import ProphetSecretary.Model.OuterTaggedPolicy
import ProphetSecretary.Model.Learner

/-!
# Fixed-outer-state reward reduction

The outer cutoff and positive cap are fixed in this theorem. The normalized
bounded learner's reward, reach, and reached-cap guarantees are explicit inputs.
The independent inner training is included in its randomized-policy seed law.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def outerFixedNormalizedResponse (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (L : Learner n (2*m)) : RandomizedPolicy n :=
  L.randomizedPolicy (P.outerTransformedInstance m hm t H)

noncomputable def outerFixedLiftedResponse (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (L : Learner n (2*m)) : RandomizedPolicy n :=
  (((outerFixedNormalizedResponse P m hm t H L).pullbackValues ((1/(H:ℝ))*·) (measurable_valueScale (1/(H:ℝ)))).pullbackValues
    (meshRound H m) (measurable_meshRound H m)).pullbackValues (capValue H) (measurable_capValue H)

/-- Conditional on fixed cutoff and scale, bounded reward and reach restore the
retained mean, with both normalized statistical and mesh errors explicit. -/
theorem outerFixedLiftedResponse_reward_of_bounded_guarantees
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (hH : (0:ℝ)<H) (L : Learner n (2*m))
    {rho Delta : ℝ} (hrho : 0≤rho)
    (hAcc : ∀ᵐ ω : (outerFixedNormalizedResponse P m hm t H L).World
        ∂(P.outerTransformedInstance m hm t H).worldLaw (outerFixedNormalizedResponse P m hm t H L).seedLaw,
      (outerFixedNormalizedResponse P m hm t H L).rule.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1)
    (hR : rho*(P.outerTransformedInstance m hm t H).expectedMaximum-Delta≤L.expectedReward (P.outerTransformedInstance m hm t H))
    (hq : ∀ i, rho≤L.reachProbability (P.outerTransformedInstance m hm t H) i) :
    rho*(P.retainedAtTag t).expectedMaximum-(H:ℝ)*Delta-rho*((H:ℝ)/m)≤
      (outerFixedLiftedResponse P m hm t H L).expectedReward (P.retainedAtTag t) := by
  have hLaw := P.outerTransformedInstance_eq_scale_mesh m hm t H hH
  have hAcc' : ∀ᵐ ω : (outerFixedNormalizedResponse P m hm t H L).World
      ∂(((P.retainedAtTag t).meshCap H hH m hm).scale (1/(H:ℝ)) (by positivity)).worldLaw
        (outerFixedNormalizedResponse P m hm t H L).seedLaw,
      (outerFixedNormalizedResponse P m hm t H L).rule.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1 := by
    rw [←hLaw]
    exact hAcc
  have hR' : rho*(((P.retainedAtTag t).meshCap H hH m hm).scale (1/(H:ℝ)) (by positivity)).expectedMaximum-Delta≤
      (outerFixedNormalizedResponse P m hm t H L).expectedReward
        (((P.retainedAtTag t).meshCap H hH m hm).scale (1/(H:ℝ)) (by positivity)) := by
    rw [←hLaw]
    exact hR
  have hq' (i : Fin n) : rho≤(outerFixedNormalizedResponse P m hm t H L).rule.reachProbability
      (((P.retainedAtTag t).meshCap H hH m hm).scale (1/(H:ℝ)) (by positivity))
        (outerFixedNormalizedResponse P m hm t H L).seedLaw i := by
    rw [←hLaw]
    exact hq i
  exact (outerFixedNormalizedResponse P m hm t H L).normalized_mesh_pullback_reward_guarantee
    (P.retainedAtTag t) H hH m hm (P.retainedAtTag_integrable_maximum hP t) hAcc' hrho hR' hq'

/-- Adding fresh online tags to the lifted response retains the same lower bound
when the selected reward is the original raw offer. -/
theorem outerFixedTaggedResponse_reward_of_bounded_guarantees
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (hH : (0:ℝ)<H) (L : Learner n (2*m))
    {rho Delta : ℝ} (hrho : 0≤rho)
    (hAcc : ∀ᵐ ω : (outerFixedNormalizedResponse P m hm t H L).World
        ∂(P.outerTransformedInstance m hm t H).worldLaw (outerFixedNormalizedResponse P m hm t H L).seedLaw,
      (outerFixedNormalizedResponse P m hm t H L).rule.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1)
    (hR : rho*(P.outerTransformedInstance m hm t H).expectedMaximum-Delta≤L.expectedReward (P.outerTransformedInstance m hm t H))
    (hq : ∀ i, rho≤L.reachProbability (P.outerTransformedInstance m hm t H) i) :
    rho*(P.retainedAtTag t).expectedMaximum-(H:ℝ)*Delta-rho*((H:ℝ)/m)≤
      ((outerFixedLiftedResponse P m hm t H L).taggedRetainedPullback t).expectedReward P :=
  (outerFixedLiftedResponse_reward_of_bounded_guarantees P hP m hm t H hH L hrho hAcc hR hq).trans
    ((outerFixedLiftedResponse P m hm t H L).taggedRetainedPullback_expectedReward_ge P hP t)

end ProphetSecretary.Statistics.Calibration
