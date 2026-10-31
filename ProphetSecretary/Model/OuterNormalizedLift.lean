import ProphetSecretary.Model.Rounding

/-!
# Lifting a guarantee stated in normalized mesh units

Scaling transports the arbitrary policy class, reach probabilities, and reached
cap acceptance. The finite cap/mesh lifting theorem then restores the original
values, with the explicit errors H Delta and rho H/m.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Model
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Policy.reachProbability_scale_pullback (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (a : ℝ) (ha : 0≤a) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (π.pullbackValues (a*·)).reachProbability P ν i=π.reachProbability (P.scale a ha) ν i := by
  have hMP := P.scaleWorld_measurePreserving a ha ν
  let E : Set (World n Seed) := {ω | π.Reaches ω.2.2 ω.1 ω.2.1 i}
  have hE : MeasurableSet E := π.measurableSet_reaches hπ (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  unfold Policy.reachProbability
  rw [←hMP.map_eq,map_measureReal_apply hMP.measurable hE]
  congr 1
  ext ω
  change ω.2.1 i≤(π.pullbackValues (a*·)).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ↔
    ω.2.1 i≤π.stoppingTime ω.2.2 Finset.univ (fun j => a*ω.1 j) ω.2.1
  rw [Policy.pullbackValues_stoppingTime]
  rfl

omit [MeasurableSpace Seed] in
lemma Policy.acceptsReachedCap_inverseScale (π : Policy Seed n) (H : ℝ≥0) (hH : (0:ℝ)<H)
    (r : Seed) (x u : Fin n → ℝ)
    (hAcc : π.AcceptsReachedCap 1 r (fun j => (1/(H:ℝ))*x j) u) :
    (π.pullbackValues ((1/(H:ℝ))*·)).AcceptsReachedCap H r x u := by
  intro i hReach hi
  have hReach' : π.Reaches r (fun j => (1/(H:ℝ))*x j) u i := by
    change u i≤(π.pullbackValues ((1/(H:ℝ))*·)).stoppingTime r Finset.univ x u at hReach
    rw [Policy.pullbackValues_stoppingTime] at hReach
    exact hReach
  have hi' : (1/(H:ℝ))*x i=(1:ℝ≥0) := by rw [hi];norm_num;field_simp
  have h := hAcc i hReach' hi'
  rw [Policy.pullbackValues_action]
  exact h

/-- `upouter:lift-conclusion` after the bounded learner's normalization by H. -/
theorem RandomizedPolicy.normalized_mesh_pullback_reward_guarantee (π : RandomizedPolicy n)
    (P : Instance n) (H : ℝ≥0) (hH : (0:ℝ)<H) (m : ℕ) (hm : 0<m)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (hAcc : ∀ᵐ ω : π.World ∂((P.meshCap H hH m hm).scale (1/(H:ℝ)) (by positivity)).worldLaw π.seedLaw,
      π.rule.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1)
    {rho Delta : ℝ} (hrho : 0≤rho)
    (hR : rho*((P.meshCap H hH m hm).scale (1/(H:ℝ)) (by positivity)).expectedMaximum-Delta≤
      π.expectedReward ((P.meshCap H hH m hm).scale (1/(H:ℝ)) (by positivity)))
    (hq : ∀ i, rho≤π.rule.reachProbability ((P.meshCap H hH m hm).scale (1/(H:ℝ)) (by positivity)) π.seedLaw i) :
    rho*P.expectedMaximum-(H:ℝ)*Delta-rho*((H:ℝ)/m)≤
      (((π.pullbackValues ((1/(H:ℝ))*·) (measurable_valueScale (1/(H:ℝ)))).pullbackValues
        (meshRound H m) (measurable_meshRound H m)).pullbackValues (capValue H) (measurable_capValue H)).expectedReward P := by
  let W := P.meshCap H hH m hm
  let σ := π.pullbackValues ((1/(H:ℝ))*·) (measurable_valueScale (1/(H:ℝ)))
  have hAc : ∀ᵐ ω : σ.World ∂W.worldLaw σ.seedLaw, σ.rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1 := by
    have hMP := W.scaleWorld_measurePreserving (1/(H:ℝ)) (show (0:ℝ)≤1/(H:ℝ) by positivity) π.seedLaw
    filter_upwards [hMP.quasiMeasurePreserving.ae hAcc] with ω hω
    exact π.rule.acceptsReachedCap_inverseScale H hH ω.2.2 ω.1 ω.2.1 hω
  have hRs := π.expectedReward_scale W (1/(H:ℝ)) (by positivity)
  have hMs := W.scale_expectedMaximum (1/(H:ℝ)) (by positivity)
  have hNorm : rho*((1/(H:ℝ))*W.expectedMaximum)-Delta≤(1/(H:ℝ))*σ.expectedReward W := by
    simpa only [W,σ,hRs,hMs] using hR
  have hMul := mul_le_mul_of_nonneg_left hNorm hH.le
  have hLeft : (H:ℝ)*(rho*((1/(H:ℝ))*W.expectedMaximum)-Delta)=rho*W.expectedMaximum-(H:ℝ)*Delta := by
    field_simp [ne_of_gt hH]
  have hRight : (H:ℝ)*((1/(H:ℝ))*σ.expectedReward W)=σ.expectedReward W := by field_simp
  rw [hLeft,hRight] at hMul
  have hReach (i : Fin n) : rho≤σ.rule.reachProbability W σ.seedLaw i := by
    change rho≤(π.rule.pullbackValues ((1/(H:ℝ))*·)).reachProbability W π.seedLaw i
    rw [Policy.reachProbability_scale_pullback π.rule π.measurable_rule W (1/(H:ℝ)) (by positivity) π.seedLaw i]
    exact hq i
  exact σ.mesh_cap_pullback_reward_guarantee P H hH m hm hP hAc hrho hMul hReach

end ProphetSecretary.Model
