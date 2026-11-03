import ProphetSecretary.Statistics.CalibratedOuter.FixedSimulation

/-!
# The raw first-positive response at a zero pilot

Inner samples and the bounded learner's seed are unused in this branch. The
online tag projection has its actual independent uniform law; its retained
first-positive reward is at least 0.997 of the retained prophet value.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def outerZeroSeedMap (m : ℕ) (L : Learner n (2*m)) (p : OuterFixedRawSeed m L) : (Fin n → ℝ) × Unit :=
  (p.2.1,())

lemma outerZeroSeedMap_measurePreserving (P : Instance n) (m : ℕ) (t : ℝ × ℝ) (L : Learner n (2*m)) :
    MeasurePreserving (outerZeroSeedMap m L) (outerFixedRawSeedLaw P m L)
      ((firstPositivePolicy n).taggedRetainedPullback t).seedLaw := by
  let μ := (P.reservoirLaw (2*m)).prod (outerTagRowsLaw n (2*m))
  letI : IsProbabilityMeasure μ := by dsimp [μ];infer_instance
  have hConst : MeasurePreserving (fun _ : L.Seed => ()) L.seedLaw (Measure.dirac ()) := by
    refine ⟨measurable_const,?_⟩
    simp only [Measure.map_const,measure_univ,one_smul]
  have hProjection := measurePreserving_snd (μ:=μ) (ν:=(Instance.clocksLaw n).prod L.seedLaw)
  exact ((MeasurePreserving.id (Instance.clocksLaw n)).prod hConst).comp hProjection

noncomputable def outerFixedZeroResponse (P : Instance n) (m : ℕ) (t : ℝ × ℝ) (L : Learner n (2*m)) : RandomizedPolicy n :=
  ((firstPositivePolicy n).taggedRetainedPullback t).pullbackSeed (outerFixedRawSeedLaw P m L)
    (outerZeroSeedMap m L) (outerZeroSeedMap_measurePreserving P m t L).measurable

lemma outerFixedZeroResponse_decide (P : Instance n) (m : ℕ) (t : ℝ × ℝ) (L : Learner n (2*m))
    (r : OuterFixedRawSeed m L) (s : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (outerFixedZeroResponse P m t L).rule.decide r s i x H=
      if 0<retainAboveTag t (x,r.2.1 i) then true else false := rfl

lemma outerFixedZeroResponse_expectedReward (P : Instance n) (m : ℕ) (t : ℝ × ℝ) (L : Learner n (2*m)) :
    (outerFixedZeroResponse P m t L).expectedReward P=
      ((firstPositivePolicy n).taggedRetainedPullback t).expectedReward P :=
  ((firstPositivePolicy n).taggedRetainedPullback t).pullbackSeed_expectedReward _ _ _
    (outerZeroSeedMap_measurePreserving P m t L) P

theorem outerFixedZeroResponse_reward_ge (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (t : ℝ × ℝ) (L : Learner n (2*m))
    (hStrict : (P.retainedAtTag t).valuesLaw.real {x | 0<Instance.maximum x}≤3/1000) :
    (997/1000:ℝ)*(P.retainedAtTag t).expectedMaximum≤(outerFixedZeroResponse P m t L).expectedReward P := by
  rw [outerFixedZeroResponse_expectedReward]
  exact (firstPositivePolicy_reward_ge_retained_fraction (P.retainedAtTag t)
    (P.retainedAtTag_integrable_maximum hP t) hStrict).trans
      ((firstPositivePolicy n).taggedRetainedPullback_expectedReward_ge P hP t)

end ProphetSecretary.Statistics.Calibration
