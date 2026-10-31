import ProphetSecretary.Model.SingleIdentity
import ProphetSecretary.Model.NumericalCompetitiveBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.HasLaw

/-!
# Waiting for a prescribed identity after a fixed time

Only the designated identity can be selected. Earlier offers, including
zeros, remain in the ordinary history. Failure to accept gives zero reward
and stopping time one. The exact duration and reward give the deterministic
prefix competitor used in `lem:nonzero`.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def RandomizedPolicy.chooseIdentityAfter (i : Fin n) (t0 : ℝ) : RandomizedPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := ⟨fun _ t j _ _ => Decidable.decide (j=i ∧ t0≤t)⟩
  measurable_rule := by
    let T := Unit × (ℝ × (Fin n × (ℝ × History n)))
    have hj : Measurable (fun z : T => z.2.2.1) := by fun_prop
    have ht : Measurable (fun z : T => z.2.1) := by fun_prop
    apply measurable_to_bool
    change MeasurableSet {z : T | Decidable.decide (z.2.2.1=i ∧ t0≤z.2.1)=true}
    simp only [decide_eq_true_eq]
    change MeasurableSet ({z : T | z.2.2.1=i} ∩ {z : T | t0≤z.2.1})
    exact (measurableSet_eq_fun hj measurable_const).inter (measurableSet_le measurable_const ht)

lemma RandomizedPolicy.chooseIdentityAfter_accepted (i : Fin n) (t0 : ℝ)
    (r : Unit) (x u : Fin n → ℝ) :
    (chooseIdentityAfter i t0).rule.accepted r Finset.univ x u=
      if t0≤u i then {i} else ∅ := by
  ext j
  by_cases ht : t0≤u i
  · by_cases hj : j=i
    · subst j
      simp [chooseIdentityAfter,Policy.accepted,Policy.action,ht]
    · simp [chooseIdentityAfter,Policy.accepted,Policy.action,hj,ht]
  · by_cases hj : j=i
    · subst j
      simp [chooseIdentityAfter,Policy.accepted,Policy.action,ht]
    · simp [chooseIdentityAfter,Policy.accepted,Policy.action,hj,ht]

lemma RandomizedPolicy.chooseIdentityAfter_stoppingTime (i : Fin n) (t0 : ℝ)
    (r : Unit) (x u : Fin n → ℝ) (hui : u i≤1) :
    (chooseIdentityAfter i t0).rule.stoppingTime r Finset.univ x u=
      if t0≤u i then u i else 1 := by
  let π := (chooseIdentityAfter i t0).rule
  have ha := chooseIdentityAfter_accepted i t0 r x u
  change π.accepted r Finset.univ x u=_ at ha
  change π.stoppingTime r Finset.univ x u=_
  by_cases ht : t0≤u i
  · rw [if_pos ht] at ha ⊢
    apply le_antisymm
    · exact π.stoppingTime_le_of_accepted r Finset.univ x u i (by rw [ha];simp)
    · apply (π.le_stoppingTime_iff r Finset.univ x u (u i)).mpr
      refine ⟨hui,?_⟩
      intro j hj
      rw [ha,Finset.mem_singleton] at hj
      subst j
      exact le_rfl
  · rw [if_neg ht] at ha ⊢
    simp [Policy.stoppingTime,Policy.stopTimes,ha]

lemma RandomizedPolicy.chooseIdentityAfter_reward (i : Fin n) (t0 : ℝ)
    (r : Unit) (x u : Fin n → ℝ) (hui : u i≤1) :
    (chooseIdentityAfter i t0).rule.reward r Finset.univ x u=
      if t0≤u i then x i else 0 := by
  let π := (chooseIdentityAfter i t0).rule
  have ha := chooseIdentityAfter_accepted i t0 r x u
  change π.accepted r Finset.univ x u=_ at ha
  have hs := chooseIdentityAfter_stoppingTime i t0 r x u hui
  change π.stoppingTime r Finset.univ x u=_ at hs
  by_cases ht : t0≤u i
  · rw [if_pos ht] at ha hs ⊢
    apply π.reward_eq_of_actualSelects
    refine ⟨⟨by rw [ha];simp,hs.symm⟩,?_⟩
    intro j hj
    have hji : j=i := by simpa only [ha,Finset.mem_singleton] using hj.1
    exact le_of_eq hji.symm
  · rw [if_neg ht] at ha ⊢
    apply π.reward_eq_zero_of_no_selection
    intro j hj
    simpa only [ha,Finset.notMem_empty] using hj.1

lemma Instance.uniformClock_restrict_Ici_eq_volume {t : ℝ} (ht : 0≤t) :
    uniformClock.restrict (Ici t)=volume.restrict (Icc t 1) := by
  rw [uniformClock,Measure.restrict_restrict measurableSet_Ici]
  congr 1
  ext u
  simp only [Set.mem_inter_iff,Set.mem_Ici,Set.mem_Icc]
  constructor
  · rintro ⟨htu,_h0,h1⟩
    exact ⟨htu,h1⟩
  · rintro ⟨htu,h1⟩
    exact ⟨htu,ht.trans htu,h1⟩

lemma Instance.uniformClock_real_Ici {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) :
    uniformClock.real (Ici t)=1-t := by
  calc
    _ = (uniformClock.restrict (Ici t)).real univ := by rw [measureReal_restrict_apply_univ]
    _ = (volume.restrict (Icc t 1)).real univ := by rw [uniformClock_restrict_Ici_eq_volume ht0]
    _ = 1-t := by
      rw [measureReal_restrict_apply_univ,Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr ht1)]

lemma Instance.uniformClock_after_duration {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) :
    (∫ u, (if t≤u then u else (1 : ℝ)) ∂uniformClock)=1/2+t-t^2/2 := by
  have hId : Integrable (fun u : ℝ => u) uniformClock := by
    apply Integrable.of_bound measurable_id.aestronglyMeasurable 1
    filter_upwards [show ∀ᵐ u ∂uniformClock, u∈Icc (0 : ℝ) 1 from ae_restrict_mem measurableSet_Icc] with u hu
    change ‖u‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg hu.1]
    exact hu.2
  let g : ℝ → ℝ := (Ici t).indicator (fun u => 1-u)
  have hG : Integrable g uniformClock := ((integrable_const (1 : ℝ)).sub hId).indicator measurableSet_Ici
  have hMean : (∫ u, g u ∂uniformClock)=(1-t)-(1-t^2)/2 := by
    rw [show (∫ u, g u ∂uniformClock)=∫ u in Ici t, (1-u : ℝ) ∂uniformClock
      from integral_indicator measurableSet_Ici]
    rw [uniformClock_restrict_Ici_eq_volume ht0,integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le ht1,
      intervalIntegral.integral_sub (f:=fun _ : ℝ => 1) (g:=fun u : ℝ => u) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const,integral_id]
    norm_num
  have hPoint : (fun u : ℝ => if t≤u then u else 1)=(fun u => 1-g u) := by
    funext u
    simp only [g,Set.indicator_apply,Set.mem_Ici]
    split_ifs <;> ring
  rw [hPoint,integral_sub (integrable_const (1 : ℝ)) hG,integral_const,probReal_univ,one_smul,hMean]
  ring

lemma RandomizedPolicy.chooseIdentityAfter_expectedDuration (P : Instance n) (i : Fin n)
    {t : ℝ} (ht0 : 0≤t) (ht1 : t≤1) :
    (chooseIdentityAfter i t).expectedDuration P=1/2+t-t^2/2 := by
  let π := chooseIdentityAfter i t
  have hClock : MeasurePreserving (fun ω : π.World => ω.2.1 i) (P.worldLaw π.seedLaw) Instance.uniformClock :=
    (measurePreserving_eval (fun _ : Fin n => Instance.uniformClock) i).comp
      (measurePreserving_fst.comp measurePreserving_snd)
  have hMeas : Measurable (fun u : ℝ => if t≤u then u else 1) :=
    measurable_id.ite (measurableSet_le measurable_const measurable_id) measurable_const
  calc
    _ = ∫ ω : π.World, (if t≤ω.2.1 i then ω.2.1 i else 1) ∂P.worldLaw π.seedLaw := by
      apply integral_congr_ae
      filter_upwards [P.world_clocks_mem_unitInterval π.seedLaw] with ω hω
      exact chooseIdentityAfter_stoppingTime i t ω.2.2 ω.1 ω.2.1 (hω i).2
    _ = ∫ u, (if t≤u then u else 1) ∂Instance.uniformClock := hClock.hasLaw.integral_comp hMeas.aestronglyMeasurable
    _ = _ := Instance.uniformClock_after_duration ht0 ht1

lemma RandomizedPolicy.chooseIdentityAfter_expectedReward_of_dirac (P : Instance n) (i : Fin n)
    {t v : ℝ} (ht0 : 0≤t) (ht1 : t≤1) (hXi : P.law i=Measure.dirac v) :
    (chooseIdentityAfter i t).expectedReward P=(1-t)*v := by
  let π := chooseIdentityAfter i t
  have hValue : MeasurePreserving (fun ω : π.World => ω.1 i) (P.worldLaw π.seedLaw) (P.law i) :=
    (measurePreserving_eval P.law i).comp measurePreserving_fst
  have hAtom : ∀ᵐ x ∂P.law i, x=v := by rw [hXi];simp
  have hX : ∀ᵐ ω : π.World ∂P.worldLaw π.seedLaw, ω.1 i=v :=
    hValue.quasiMeasurePreserving.ae hAtom
  have hClock : MeasurePreserving (fun ω : π.World => ω.2.1 i) (P.worldLaw π.seedLaw) Instance.uniformClock :=
    (measurePreserving_eval (fun _ : Fin n => Instance.uniformClock) i).comp
      (measurePreserving_fst.comp measurePreserving_snd)
  have hMeas : Measurable ((Ici t).indicator (fun _ : ℝ => v)) := measurable_const.indicator measurableSet_Ici
  calc
    _ = ∫ ω : π.World, (Ici t).indicator (fun _ => v) (ω.2.1 i) ∂P.worldLaw π.seedLaw := by
      apply integral_congr_ae
      filter_upwards [P.world_clocks_mem_unitInterval π.seedLaw,hX] with ω hω hx
      change (chooseIdentityAfter i t).rule.reward ω.2.2 Finset.univ ω.1 ω.2.1=_
      rw [chooseIdentityAfter_reward i t ω.2.2 ω.1 ω.2.1 (hω i).2,hx]
      simp only [Set.indicator_apply,Set.mem_Ici]
    _ = ∫ u, (Ici t).indicator (fun _ => v) u ∂Instance.uniformClock := hClock.hasLaw.integral_comp hMeas.aestronglyMeasurable
    _ = (1-t)*v := by rw [integral_indicator measurableSet_Ici,integral_const,smul_eq_mul,measureReal_restrict_apply_univ,Instance.uniformClock_real_Ici ht0 ht1]

/-- A causal competitor using one known deterministic offer; other laws are
unrestricted subject to the finite benchmark integrability assumption. -/
theorem Instance.optimalScalarValue_ge_identityAfter (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {t v w c : ℝ}
    (ht0 : 0≤t) (ht1 : t≤1) (hXi : P.law i=Measure.dirac v) (hw : 0≤w) (hc : 0≤c) :
    w*((1-t)*v)+c*(1/2+t-t^2/2)≤optimalScalarValue P w c := by
  let π := RandomizedPolicy.chooseIdentityAfter i t
  have hJ := π.scalarObjective_eq P hP w c
  rw [RandomizedPolicy.chooseIdentityAfter_expectedReward_of_dirac P i ht0 ht1 hXi,
    RandomizedPolicy.chooseIdentityAfter_expectedDuration P i ht0 ht1] at hJ
  exact hJ.symm.le.trans (scalarObjective_le_optimal π P hP hw hc)

/-- At t=1−C the expected duration is strictly greater than C. -/
theorem Instance.optimalScalarValue_ge_knownOffer_at_globalRatio (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {v w c : ℝ}
    (hXi : P.law i=Measure.dirac v) (hw : 0≤w) (hc : 0≤c) :
    w*optimalCompetitiveRatio*v+c*(1-optimalCompetitiveRatio^2/2)≤optimalScalarValue P w c := by
  have h := P.optimalScalarValue_ge_identityAfter hP i
    (sub_nonneg.mpr optimalCompetitiveRatio_le_one) (by linarith only [optimalCompetitiveRatio_nonnegative]) hXi hw hc
  convert h using 1
  ring

lemma globalRatio_knownOffer_duration_strict :
    optimalCompetitiveRatio<1-optimalCompetitiveRatio^2/2 := by
  nlinarith only [optimalCompetitiveRatio_quadratic_strict]

end ProphetSecretary.Model
