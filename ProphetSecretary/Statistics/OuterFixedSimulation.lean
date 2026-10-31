import ProphetSecretary.Statistics.OuterFixedResponse
import ProphetSecretary.Model.PolicySeedTransport
import ProphetSecretary.Statistics.OuterLearner

/-!
# Fresh raw blocks simulate a fixed outer response

For fixed cutoff and positive scale, independent raw inner samples and their
independent tags map to the bounded learner's actual training law. Online tags
remain a separate factor and the bounded learner retains its own seed.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n : ℕ}

abbrev OuterFixedRawSeed (m : ℕ) (L : Learner n (4*m)) :=
  (Reservoir n (4*m) × (Fin (4*m) → Fin n → ℝ)) × ((Fin n → ℝ) × L.Seed)

noncomputable def outerFixedRawSeedLaw (P : Instance n) (m : ℕ) (L : Learner n (4*m)) : Measure (OuterFixedRawSeed m L) :=
  ((P.reservoirLaw (4*m)).prod (outerTagRowsLaw n (4*m))).prod ((Instance.clocksLaw n).prod L.seedLaw)

instance outerFixedRawSeedLaw_probability (P : Instance n) (m : ℕ) (L : Learner n (4*m)) :
    IsProbabilityMeasure (outerFixedRawSeedLaw P m L) := by unfold outerFixedRawSeedLaw;infer_instance

noncomputable def outerFixedRawSeedMap (m : ℕ) (t : ℝ × ℝ) (H : ℝ) (L : Learner n (4*m))
    (p : OuterFixedRawSeed m L) : (Fin n → ℝ) × (Reservoir n (4*m) × L.Seed) :=
  (p.2.1,(outerTransformedReservoir m t H p.1,p.2.2))

lemma outerFixedRawSeedMap_measurePreserving (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (L : Learner n (4*m)) :
    MeasurePreserving (outerFixedRawSeedMap m t H L) (outerFixedRawSeedLaw P m L)
      ((outerFixedLiftedResponse P m hm t H L).taggedRetainedPullback t).seedLaw := by
  let μ := (P.reservoirLaw (4*m)).prod (outerTagRowsLaw n (4*m))
  let ν := Instance.clocksLaw n
  letI : IsProbabilityMeasure μ := by dsimp [μ];infer_instance
  have h0 := (measurePreserving_prodAssoc μ ν L.seedLaw).symm
    (MeasurableEquiv.prodAssoc : (((Reservoir n (4*m) × (Fin (4*m) → Fin n → ℝ)) × (Fin n → ℝ)) × L.Seed) ≃ᵐ
      ((Reservoir n (4*m) × (Fin (4*m) → Fin n → ℝ)) × ((Fin n → ℝ) × L.Seed)))
  have h1 := (Measure.measurePreserving_swap (μ:=μ) (ν:=ν)).prod (MeasurePreserving.id L.seedLaw)
  have h2 := measurePreserving_prodAssoc ν μ L.seedLaw
  let Q := P.outerTransformedInstance m hm t H
  have hFresh : MeasurePreserving (outerTransformedReservoir (n:=n) (q:=4*m) m t H) μ (Q.reservoirLaw (4*m)) :=
    outerTransformedReservoir_measurePreserving P (4*m) m hm t H
  have h3 := (MeasurePreserving.id ν).prod (hFresh.prod (MeasurePreserving.id L.seedLaw))
  exact h3.comp (h2.comp (h1.comp h0))

noncomputable def outerFixedTransplantedResponse (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (L : Learner n (4*m)) : RandomizedPolicy n :=
  ((outerFixedLiftedResponse P m hm t H L).taggedRetainedPullback t).pullbackSeed
    (outerFixedRawSeedLaw P m L) (outerFixedRawSeedMap m t H L)
      (outerFixedRawSeedMap_measurePreserving P m hm t H L).measurable

lemma outerFixedTransplantedResponse_expectedReward (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (L : Learner n (4*m)) :
    (outerFixedTransplantedResponse P m hm t H L).expectedReward P=
      ((outerFixedLiftedResponse P m hm t H L).taggedRetainedPullback t).expectedReward P :=
  ((outerFixedLiftedResponse P m hm t H L).taggedRetainedPullback t).pullbackSeed_expectedReward
    _ _ _ (outerFixedRawSeedMap_measurePreserving P m hm t H L) P

noncomputable def outerFixedRawResponse (P : Instance n) (m : ℕ)
    (t : ℝ × ℝ) (H : ℝ≥0) (L : Learner n (4*m)) : RandomizedPolicy n where
  Seed := OuterFixedRawSeed m L
  seedLaw := outerFixedRawSeedLaw P m L
  rule := L.policy.pullbackValuesBy
    (fun p => (outerTransformedReservoir m t H p.1,p.2.2))
    (fun p i x => outerMeshDisplay m H (retainAboveTag t (x,p.2.1 i)))
  measurable_rule := by
    have hInput : Measurable (fun p : OuterFixedRawSeed m L => ((t,(H:ℝ)),p.1)) := measurable_const.prodMk measurable_fst
    have hTraining : Measurable (fun p : OuterFixedRawSeed m L => outerTransformedReservoir m t H p.1) := by
      simpa only [Function.comp_def] using (measurable_outerTransformedReservoir m).comp hInput
    apply L.policy.pullbackValuesBy_isMeasurable L.policy_isMeasurable _
      (hTraining.prodMk (measurable_snd.comp measurable_snd))
    intro i
    have hTag : Measurable (fun p : OuterFixedRawSeed m L × ℝ => p.1.2.1 i) :=
      (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
    have hRet : Measurable (fun p : OuterFixedRawSeed m L × ℝ => retainAboveTag t (p.2,p.1.2.1 i)) :=
      measurable_retainAboveTag.comp (measurable_const.prodMk (measurable_snd.prodMk hTag))
    exact (measurable_outerUnitMesh m).comp (hRet.div_const (H:ℝ))

lemma outerFixedRawResponse_action (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (hH : (0:ℝ)<H) (L : Learner n (4*m))
    (p : OuterFixedRawSeed m L) (D : Finset (Fin n)) (x u : Fin n → ℝ) (hx : ∀ i, 0≤x i) (j : Fin n) :
    (outerFixedRawResponse P m t H L).rule.action p D x u j=
      (outerFixedTransplantedResponse P m hm t H L).rule.action p D x u j := by
  change (L.policy.pullbackValuesBy
      (fun p : OuterFixedRawSeed m L => (outerTransformedReservoir m t H p.1,p.2.2))
      (fun p i v => outerMeshDisplay m H (retainAboveTag t (v,p.2.1 i)))).action p D x u j=
    ((((L.policy.pullbackValues ((1/(H:ℝ))*·)).pullbackValues (meshRound H m)).pullbackValues (capValue H)).pullbackValuesBy
      Prod.snd (fun (r : (Fin n → ℝ) × (Reservoir n (4*m) × L.Seed)) i v => retainAboveTag t (v,r.1 i))).action
        (p.2.1,(outerTransformedReservoir m t H p.1,p.2.2)) D x u j
  simp only [Policy.pullbackValuesBy_action,Policy.pullbackValues_action,Function.comp_def]
  congr 1
  funext i
  rw [outerMeshDisplay_eq_mesh m H hH (retainAboveTag_nonneg t _ (hx i))]
  ring

lemma outerFixedRawResponse_reward (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (hH : (0:ℝ)<H) (L : Learner n (4*m))
    (p : OuterFixedRawSeed m L) (D : Finset (Fin n)) (x u : Fin n → ℝ) (hx : ∀ i, 0≤x i) :
    (outerFixedRawResponse P m t H L).rule.reward p D x u=
      (outerFixedTransplantedResponse P m hm t H L).rule.reward p D x u := by
  have hAcc : (outerFixedRawResponse P m t H L).rule.accepted p D x u=
      (outerFixedTransplantedResponse P m hm t H L).rule.accepted p D x u := by
    ext i
    simp only [Policy.mem_accepted,outerFixedRawResponse_action P m hm t H hH L p D x u hx i]
  have hStop : (outerFixedRawResponse P m t H L).rule.stoppingTime p D x u=
      (outerFixedTransplantedResponse P m hm t H L).rule.stoppingTime p D x u := by
    simp only [Policy.stoppingTime,Policy.stopTimes,hAcc]
  have hSel (i : Fin n) : (outerFixedRawResponse P m t H L).rule.ActualSelects p D x u i ↔
      (outerFixedTransplantedResponse P m hm t H L).rule.ActualSelects p D x u i := by
    simp only [Policy.ActualSelects,Policy.Selects,hAcc,hStop]
  unfold Policy.reward
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (outerFixedRawResponse P m t H L).rule.ActualSelects p D x u i
  · simp only [if_pos hi,if_pos ((hSel i).mp hi)]
  · simp only [if_neg hi,if_neg (fun h => hi ((hSel i).mpr h))]

/-- The actual raw fresh-block policy has the ideal normalized response's reward. -/
lemma outerFixedRawResponse_expectedReward (P : Instance n) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (hH : (0:ℝ)<H) (L : Learner n (4*m)) :
    (outerFixedRawResponse P m t H L).expectedReward P=
      ((outerFixedLiftedResponse P m hm t H L).taggedRetainedPullback t).expectedReward P := by
  rw [←outerFixedTransplantedResponse_expectedReward P m hm t H L]
  apply integral_congr_ae
  have hX := (measurePreserving_fst (μ:=P.valuesLaw) (ν:=(Instance.clocksLaw n).prod (outerFixedRawSeedLaw P m L))).quasiMeasurePreserving.ae P.ae_nonnegative
  filter_upwards [hX] with ω hω
  exact outerFixedRawResponse_reward P m hm t H hH L ω.2.2 Finset.univ ω.1 ω.2.1 hω

/-- The fixed-outer guarantee for the actual independent raw sampling experiment. -/
theorem outerFixedRawResponse_reward_of_bounded_guarantees
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (m : ℕ) (hm : 0<m)
    (t : ℝ × ℝ) (H : ℝ≥0) (hH : (0:ℝ)<H) (L : Learner n (4*m))
    {rho Delta : ℝ} (hrho : 0≤rho)
    (hAcc : ∀ᵐ ω : (outerFixedNormalizedResponse P m hm t H L).World
        ∂(P.outerTransformedInstance m hm t H).worldLaw (outerFixedNormalizedResponse P m hm t H L).seedLaw,
      (outerFixedNormalizedResponse P m hm t H L).rule.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1)
    (hR : rho*(P.outerTransformedInstance m hm t H).expectedMaximum-Delta≤L.expectedReward (P.outerTransformedInstance m hm t H))
    (hq : ∀ i, rho≤L.reachProbability (P.outerTransformedInstance m hm t H) i) :
    rho*(P.retainedAtTag t).expectedMaximum-(H:ℝ)*Delta-rho*((H:ℝ)/m)≤
      (outerFixedRawResponse P m t H L).expectedReward P := by
  rw [outerFixedRawResponse_expectedReward P m hm t H hH L]
  exact outerFixedTaggedResponse_reward_of_bounded_guarantees P hP m hm t H hH L hrho hAcc hR hq

end ProphetSecretary.Statistics
