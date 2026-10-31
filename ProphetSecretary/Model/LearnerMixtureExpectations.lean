import ProphetSecretary.Model.LearnerMixture
import ProphetSecretary.Model.ExtendedExpectations

/-!
# Rewards of an independent mixture of training procedures

The branch is selected before training, independently of every sample, offer
and arrival time. The same branch-specific adaptive transcript and online
callback are used. Extended nonnegative expectations retain infinite rewards;
the real-valued formula follows when the maximum is integrable.
-/

open MeasureTheory
open scoped ENNReal
namespace ProphetSecretary.Model.Learner
variable {n k : ℕ}

noncomputable def extendedExpectedReward (L : Learner n k) (P : Instance n) : ℝ≥0∞ :=
  (L.randomizedPolicy P).extendedExpectedReward P

def mixWorldInl (L R : Learner n k)
    (v : World n (Reservoir n k × L.Seed)) : World n (Reservoir n k × (L.Seed ⊕ R.Seed)) :=
  (v.1,(v.2.1,(v.2.2.1,Sum.inl v.2.2.2)))

def mixWorldInr (L R : Learner n k)
    (v : World n (Reservoir n k × R.Seed)) : World n (Reservoir n k × (L.Seed ⊕ R.Seed)) :=
  (v.1,(v.2.1,(v.2.2.1,Sum.inr v.2.2.2)))

lemma mixWorldInl_measurePreserving (L R : Learner n k) (P : Instance n) :
    MeasurePreserving (mixWorldInl L R) (P.worldLaw ((P.reservoirLaw k).prod L.seedLaw))
      (P.worldLaw ((P.reservoirLaw k).prod (Measure.map Sum.inl L.seedLaw))) := by
  have h : MeasurePreserving (Sum.inl : L.Seed → L.Seed ⊕ R.Seed) L.seedLaw
      (Measure.map Sum.inl L.seedLaw) := ⟨measurable_inl,rfl⟩
  exact (MeasurePreserving.id P.valuesLaw).prod
    ((MeasurePreserving.id (Instance.clocksLaw n)).prod
      ((MeasurePreserving.id (P.reservoirLaw k)).prod h))

lemma mixWorldInr_measurePreserving (L R : Learner n k) (P : Instance n) :
    MeasurePreserving (mixWorldInr L R) (P.worldLaw ((P.reservoirLaw k).prod R.seedLaw))
      (P.worldLaw ((P.reservoirLaw k).prod (Measure.map Sum.inr R.seedLaw))) := by
  have h : MeasurePreserving (Sum.inr : R.Seed → L.Seed ⊕ R.Seed) R.seedLaw
      (Measure.map Sum.inr R.seedLaw) := ⟨measurable_inr,rfl⟩
  exact (MeasurePreserving.id P.valuesLaw).prod
    ((MeasurePreserving.id (Instance.clocksLaw n)).prod
      ((MeasurePreserving.id (P.reservoirLaw k)).prod h))

lemma mix_worldLaw (L R : Learner n k) (a b : ℝ≥0∞) (_hab : a+b=1) (P : Instance n) :
    P.worldLaw ((P.reservoirLaw k).prod
      (a • Measure.map (Sum.inl : L.Seed → L.Seed ⊕ R.Seed) L.seedLaw+
       b • Measure.map (Sum.inr : R.Seed → L.Seed ⊕ R.Seed) R.seedLaw))=
      a • P.worldLaw ((P.reservoirLaw k).prod (Measure.map Sum.inl L.seedLaw))+
      b • P.worldLaw ((P.reservoirLaw k).prod (Measure.map Sum.inr R.seedLaw)) := by
  haveI : IsProbabilityMeasure (Measure.map (Sum.inl : L.Seed → L.Seed ⊕ R.Seed) L.seedLaw) :=
    Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map (Sum.inr : R.Seed → L.Seed ⊕ R.Seed) R.seedLaw) :=
    Measure.isProbabilityMeasure_map measurable_inr.aemeasurable
  simp only [Instance.worldLaw,Measure.prod_add,Measure.prod_smul_right]

theorem mix_extendedExpectedReward (L R : Learner n k) (a b : ℝ≥0∞)
    (hab : a+b=1) (P : Instance n) :
    (L.mix R a b hab).extendedExpectedReward P=
      a*L.extendedExpectedReward P+b*R.extendedExpectedReward P := by
  let M := L.mix R a b hab
  let F : World n (Reservoir n k × (L.Seed ⊕ R.Seed)) → ℝ :=
    (M.randomizedPolicy P).realizedReward
  have hF : Measurable F := (M.randomizedPolicy P).measurable_realizedReward
  have hLeft : (∫⁻ v, ENNReal.ofReal (F v)
      ∂P.worldLaw ((P.reservoirLaw k).prod (Measure.map Sum.inl L.seedLaw)))=
      L.extendedExpectedReward P := by
    rw [← (mixWorldInl_measurePreserving L R P).lintegral_comp hF.ennreal_ofReal]
    apply lintegral_congr
    intro v
    congr 1
    exact mix_reward_inl L R a b hab v.2.2.1 v.2.2.2 Finset.univ v.1 v.2.1
  have hRight : (∫⁻ v, ENNReal.ofReal (F v)
      ∂P.worldLaw ((P.reservoirLaw k).prod (Measure.map Sum.inr R.seedLaw)))=
      R.extendedExpectedReward P := by
    rw [← (mixWorldInr_measurePreserving L R P).lintegral_comp hF.ennreal_ofReal]
    apply lintegral_congr
    intro v
    congr 1
    exact mix_reward_inr L R a b hab v.2.2.1 v.2.2.2 Finset.univ v.1 v.2.1
  change (∫⁻ v : World n (Reservoir n k × (L.Seed ⊕ R.Seed)), ENNReal.ofReal (F v)
    ∂P.worldLaw ((P.reservoirLaw k).prod
      (a • Measure.map (Sum.inl : L.Seed → L.Seed ⊕ R.Seed) L.seedLaw+
       b • Measure.map (Sum.inr : R.Seed → L.Seed ⊕ R.Seed) R.seedLaw)))=_
  rw [mix_worldLaw L R a b hab P,lintegral_add_measure,
    lintegral_smul_measure,lintegral_smul_measure,hLeft,hRight]
  rfl

lemma extendedExpectedReward_eq_of_integrable (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    L.extendedExpectedReward P=ENNReal.ofReal (L.expectedReward P) :=
  (L.randomizedPolicy P).extendedExpectedReward_eq_of_integrable P hP

theorem mix_expectedReward (L R : Learner n k) (a b : ℝ≥0∞)
    (hab : a+b=1) (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    (L.mix R a b hab).expectedReward P=
      a.toReal*L.expectedReward P+b.toReal*R.expectedReward P := by
  have hFinite : a+b≠⊤ := by rw [hab]; exact ENNReal.one_ne_top
  have ha : a≠⊤ := (ENNReal.add_ne_top.mp hFinite).1
  have hb : b≠⊤ := (ENNReal.add_ne_top.mp hFinite).2
  have hL : 0≤L.expectedReward P := (L.randomizedPolicy P).expectedReward_nonnegative P
  have hR : 0≤R.expectedReward P := (R.randomizedPolicy P).expectedReward_nonnegative P
  have hM : 0≤(L.mix R a b hab).expectedReward P :=
    ((L.mix R a b hab).randomizedPolicy P).expectedReward_nonnegative P
  have h := mix_extendedExpectedReward L R a b hab P
  rw [extendedExpectedReward_eq_of_integrable _ P hP,
    extendedExpectedReward_eq_of_integrable L P hP,
    extendedExpectedReward_eq_of_integrable R P hP] at h
  have hReal := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_add (ENNReal.mul_ne_top ha ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top hb ENNReal.ofReal_ne_top),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hM,ENNReal.toReal_ofReal hL,ENNReal.toReal_ofReal hR] using hReal

end ProphetSecretary.Model.Learner
