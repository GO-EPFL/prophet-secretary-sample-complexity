import ProphetSecretary.Model.LearnerConditioning
import ProphetSecretary.Model.EmpiricalConditionalValues
import Mathlib.Probability.HasLaw

/-!
# Conditioning a data-selected scalar score on training

The selected weight is held fixed when the independent online instance is
integrated. Bounded weight multiplication proves joint integrability before
Fubini is applied. The identity permits any independent probability data
law and any measurable learner; no fixed-weight unbiasedness is asserted.
-/

open MeasureTheory Set Filter
namespace ProphetSecretary.Model
variable {n k : ℕ}

noncomputable def Learner.selectedScore (L : Learner n k) (W : Reservoir n k × L.Seed → ℝ)
    (C : ℝ) (ω : World n (Reservoir n k × L.Seed)) : ℝ :=
  W ω.2.2*(L.policy.reward ω.2.2 Finset.univ ω.1 ω.2.1-C*Instance.maximum ω.1)+
    (1-W ω.2.2)*(L.policy.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1-C)

lemma Learner.measurable_selectedScore (L : Learner n k) {W : Reservoir n k × L.Seed → ℝ}
    (hW : Measurable W) (C : ℝ) : Measurable (L.selectedScore W C) := by
  have hWeight : Measurable (fun ω : World n (Reservoir n k × L.Seed) => W ω.2.2) :=
    hW.comp (measurable_snd.comp measurable_snd)
  have hR : Measurable (fun ω : World n (Reservoir n k × L.Seed) =>
      L.policy.reward ω.2.2 Finset.univ ω.1 ω.2.1) :=
    L.policy.measurable_reward L.policy_isMeasurable
    (measurable_snd.comp measurable_snd)
    (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) Finset.univ
  have hT : Measurable (fun ω : World n (Reservoir n k × L.Seed) =>
      L.policy.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1) :=
    L.policy.measurable_stoppingTime L.policy_isMeasurable
    (measurable_snd.comp measurable_snd)
    (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) Finset.univ
  exact (hWeight.mul (hR.sub ((Instance.measurable_maximum.comp measurable_fst).const_mul C))).add
    ((measurable_const.sub hWeight).mul (hT.sub_const C))

theorem Learner.integral_selectedScore_eq_frozen (L : Learner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D]
    (W : Reservoir n k × L.Seed → ℝ) (hW : Measurable W) (hRange : ∀ d, W d∈Icc (0 : ℝ) 1) (C : ℝ) :
    (∫ ω : World n (Reservoir n k × L.Seed),
      W ω.2.2*(L.policy.reward ω.2.2 Finset.univ ω.1 ω.2.1-C*Instance.maximum ω.1)+
        (1-W ω.2.2)*(L.policy.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1-C) ∂P.worldLaw D) =
    ∫ d, (L.frozenRandomizedPolicy d.1 d.2).scalarObjective P (W d) (1-W d)-
      C*(W d*P.expectedMaximum+1-W d) ∂D := by
  let π := L.randomizedPolicyWithDataLaw D
  let H := fun ω : World n (Reservoir n k × L.Seed) =>
    W ω.2.2*(L.policy.reward ω.2.2 Finset.univ ω.1 ω.2.1-C*Instance.maximum ω.1)+
      (1-W ω.2.2)*(L.policy.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1-C)
  have hMeas : Measurable H := L.measurable_selectedScore hW C
  have hMP := P.seedFirstWorld_measurePreserving D
  have hR := hMP.integrable_comp_of_integrable (π.integrable_realizedReward P hP)
  have hT := hMP.integrable_comp_of_integrable (π.integrable_realizedDuration P)
  have hVal : MeasurePreserving (fun ω : World n (Reservoir n k × L.Seed) => ω.1)
      (P.worldLaw D) P.valuesLaw := by
    unfold Instance.worldLaw
    exact measurePreserving_fst
  have hX := hMP.integrable_comp_of_integrable (hVal.integrable_comp_of_integrable hP)
  have hWeightBound : ∀ᵐ z : (Reservoir n k × L.Seed) × World n Unit ∂D.prod (P.worldLaw (Measure.dirac ())),
      ‖W z.1‖≤1 := Eventually.of_forall (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hRange z.1).1];exact (hRange z.1).2)
  have hComplementBound : ∀ᵐ z : (Reservoir n k × L.Seed) × World n Unit ∂D.prod (P.worldLaw (Measure.dirac ())),
      ‖1-W z.1‖≤1 := Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hRange z.1).2)]
        linarith only [(hRange z.1).1])
  have hFirst := (hR.sub (hX.const_mul C)).bdd_mul (hW.comp measurable_fst).aestronglyMeasurable hWeightBound
  have hSecond := (hT.sub (integrable_const C)).bdd_mul
    (measurable_const.sub (hW.comp measurable_fst)).aestronglyMeasurable hComplementBound
  have hJoint : Integrable (fun z => H (Instance.seedFirstWorld z)) (D.prod (P.worldLaw (Measure.dirac ()))) :=
    hFirst.add hSecond
  have hMean := hMP.hasLaw.integral_comp hMeas.aestronglyMeasurable
  change (∫ ω, H ω ∂P.worldLaw D)=_
  rw [← hMean]
  change (∫ z : (Reservoir n k × L.Seed) × World n Unit, H (Instance.seedFirstWorld z)
    ∂D.prod (P.worldLaw (Measure.dirac ())))=_
  rw [integral_prod _ hJoint]
  apply integral_congr_ae
  filter_upwards [] with d
  let σ := L.frozenRandomizedPolicy d.1 d.2
  let R0 := fun ω : World n Unit => (L.frozenRule d.1 d.2).reward ω.2.2 Finset.univ ω.1 ω.2.1
  let T0 := fun ω : World n Unit => (L.frozenRule d.1 d.2).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
  have hRF : Integrable R0 (P.worldLaw (Measure.dirac ())) := σ.integrable_realizedReward P hP
  have hTF : Integrable T0 (P.worldLaw (Measure.dirac ())) := σ.integrable_realizedDuration P
  have hVF : MeasurePreserving (fun ω : World n Unit => ω.1) (P.worldLaw (Measure.dirac ())) P.valuesLaw :=
    measurePreserving_fst
  have hXF : Integrable (fun ω : World n Unit => Instance.maximum ω.1) (P.worldLaw (Measure.dirac ())) :=
    hVF.integrable_comp_of_integrable hP
  have hXM : (∫ ω : World n Unit, Instance.maximum ω.1 ∂P.worldLaw (Measure.dirac ()))=P.expectedMaximum :=
    hVF.hasLaw.integral_comp Instance.measurable_maximum.aestronglyMeasurable
  have hRS : Integrable (fun ω : World n Unit => W d*(R0 ω-C*Instance.maximum ω.1))
      (P.worldLaw (Measure.dirac ())) := (hRF.sub (hXF.const_mul C)).const_mul (W d)
  have hTS : Integrable (fun ω : World n Unit => (1-W d)*(T0 ω-C))
      (P.worldLaw (Measure.dirac ())) := (hTF.sub (integrable_const C)).const_mul (1-W d)
  change (∫ ω : World n Unit, W d*(R0 ω-C*Instance.maximum ω.1)+
      (1-W d)*(T0 ω-C) ∂P.worldLaw (Measure.dirac ())) =
    σ.scalarObjective P (W d) (1-W d)-C*(W d*P.expectedMaximum+1-W d)
  rw [integral_add hRS hTS,integral_const_mul,integral_const_mul,
    integral_sub hRF (hXF.const_mul C),integral_sub hTF (integrable_const C),
    integral_const_mul,hXM,integral_const,probReal_univ,one_smul,σ.scalarObjective_eq P hP]
  change W d*(σ.expectedReward P-C*P.expectedMaximum)+(1-W d)*(σ.expectedDuration P-C)=_
  ring

end ProphetSecretary.Model
