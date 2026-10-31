import ProphetSecretary.Limiting.CutoffCountJointLaw
import ProphetSecretary.Probability.RandomMeasureLaw
import Mathlib.Probability.Independence.Integration

/-!
# Finite marked Poisson superposition

The entire anonymous counting measure has the summed-intensity Poisson law.
Generation labels and future counts remain analytical data.
-/
open MeasureTheory ProbabilityTheory Set Filter Complex
open scoped Classical NNReal ENNReal BigOperators
namespace ProphetSecretary.Limiting
variable {ι : Type*} [Fintype ι]
noncomputable def finiteConfigurationsLaw (μ : ι → FiniteMeasure ℝ) :
    Measure (ι → Configuration) := Measure.pi (fun i => configurationLaw (μ i))
instance finiteConfigurationsLaw_isProbability (μ : ι → FiniteMeasure ℝ) :
    IsProbabilityMeasure (finiteConfigurationsLaw μ) := by
  unfold finiteConfigurationsLaw
  infer_instance
noncomputable def finiteCountingMeasure (ω : ι → Configuration) : Measure Point :=
  ∑ i, countingMeasure (ω i)
lemma measurable_finiteCountingMeasure : Measurable (finiteCountingMeasure (ι := ι)) :=
  Finset.measurable_fun_sum _ (fun i _ => measurable_countingMeasure.comp (measurable_pi_apply i))
lemma finiteCountingMeasure_univ (ω : ι → Configuration) :
    finiteCountingMeasure ω univ = ((∑ i, (ω i).1 : ℕ) : ℝ≥0∞) := by
  simp [finiteCountingMeasure,Measure.coe_finsetSum,Finset.sum_apply,countingMeasure_univ]
lemma intensity_finiteSum (μ : ι → FiniteMeasure ℝ) :
    intensity (∑ i, μ i) = ∑ i, intensity (μ i) := by
  unfold intensity
  rw [FiniteMeasure.toMeasure_sum]
  have h (s : Finset ι) : Model.Instance.uniformClock.prod (∑ i ∈ s, (μ i : Measure ℝ)) =
      ∑ i ∈ s, Model.Instance.uniformClock.prod (μ i : Measure ℝ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => rw [Finset.sum_insert hi,Measure.prod_add,ih,Finset.sum_insert hi]
  exact h Finset.univ
lemma finiteConfigurations_generating_functional (μ : ι → FiniteMeasure ℝ) (g : Point → ℂ)
    (hg : Measurable g) (hb : ∀ p, ‖g p‖ ≤ 1) :
    (∫ ω, ∏ i, pointProd g (ω i) ∂finiteConfigurationsLaw μ) =
      ∫ ω, pointProd g ω ∂configurationLaw (∑ i, μ i) := by
  have hG := measurable_pointProd hg
  have hI : iIndepFun (fun i (ω : ι → Configuration) => pointProd g (ω i))
      (finiteConfigurationsLaw μ) :=
    (iIndepFun_pi (μ := fun i => configurationLaw (μ i))
      (X := fun _ => id) (fun _ => aemeasurable_id)).comp (fun _ => pointProd g) (fun _ => hG)
  have hp := hI.integral_fun_prod_eq_prod_integral
    (fun i => (hG.comp (measurable_pi_apply i)).aestronglyMeasurable)
  change (∫ ω, ∏ i, pointProd g (ω i) ∂finiteConfigurationsLaw μ) = _ at hp
  have hInt (i : ι) : Integrable (fun p => g p-1) (intensity (μ i)) :=
    (Integrable.of_bound hg.aestronglyMeasurable 1 (Eventually.of_forall hb)).sub (integrable_const 1)
  rw [hp,generating_functional_intensity (∑ i, μ i) g hg hb,intensity_finiteSum,
    integral_finsetSum_measure (f := fun p => g p-1) (fun i _ => hInt i),Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  have he : MeasurePreserving (fun ω : ι → Configuration => ω i)
      (finiteConfigurationsLaw μ) (configurationLaw (μ i)) := measurePreserving_eval _ i
  have hi := he.hasLaw.integral_comp hG.aestronglyMeasurable
  change (∫ ω, pointProd g (ω i) ∂finiteConfigurationsLaw μ) = _ at hi
  exact hi.trans (generating_functional_intensity (μ i) g hg hb)
lemma finiteConfigurations_joint_generating {κ : Type*} [Fintype κ]
    (μ : ι → FiniteMeasure ℝ) (S : κ → Set Point) (hS : ∀ j, MeasurableSet (S j))
    (z : κ → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1) :
    (∫ ω, ∏ j, z j ^ (∑ i, pointCount (S j) (ω i)) ∂finiteConfigurationsLaw μ) =
      ∫ ω, ∏ j, z j ^ pointCount (S j) ω ∂configurationLaw (∑ i, μ i) := by
  have hm : Measurable (fun p => ∏ j, pointFactor (S j) (z j) p) :=
    Finset.measurable_fun_prod _ (fun j _ => measurable_pointFactor (hS j) (z j))
  have hb (p : Point) : ‖∏ j, pointFactor (S j) (z j) p‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
      (fun j _ => pointFactor_norm_le_one (S j) (hz j) p)
  have he := finiteConfigurations_generating_functional μ _ hm hb
  simp_rw [pointProd_prod_pointFactor] at he
  have hprod (ω : ι → Configuration) :
      (∏ j, z j ^ (∑ i, pointCount (S j) (ω i))) =
        ∏ i, ∏ j, z j ^ pointCount (S j) (ω i) := by
    simp_rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_comm
  simpa only [hprod] using he
lemma finiteConfigurations_counts_joint_law {κ : Type*} [Fintype κ]
    (μ : ι → FiniteMeasure ℝ) (S : κ → Set Point) (hS : ∀ j, MeasurableSet (S j)) :
    (finiteConfigurationsLaw μ).map (fun ω j => ((∑ i, pointCount (S j) (ω i) : ℕ) : ℝ)) =
      (configurationLaw (∑ i, μ i)).map (fun ω j => (pointCount (S j) ω : ℝ)) := by
  let f := fun (ω : ι → Configuration) j => ((∑ i, pointCount (S j) (ω i) : ℕ) : ℝ)
  let h := fun (ω : Configuration) j => (pointCount (S j) ω : ℝ)
  have hf : Measurable f := measurable_pi_lambda _ (fun j =>
    (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp
      (Finset.measurable_fun_sum _ (fun i _ => (measurable_pointCount (hS j)).comp (measurable_pi_apply i))))
  have hh : Measurable h := measurable_pi_lambda _ (fun j =>
    (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp (measurable_pointCount (hS j)))
  let e := MeasurableEquiv.toLp 2 (κ → ℝ)
  change (finiteConfigurationsLaw μ).map f = (configurationLaw (∑ i, μ i)).map h
  apply MeasurableEquiv.map_measurableEquiv_injective e
  rw [Measure.map_map e.measurable hf,Measure.map_map e.measurable hh]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply,charFun_apply,integral_map (e.measurable.comp hf).aemeasurable (by fun_prop),
    integral_map (e.measurable.comp hh).aemeasurable (by fun_prop)]
  simp only [PiLp.inner_apply,Real.inner_apply,f,h]
  dsimp only [Function.comp_def,e,MeasurableEquiv.coe_toLp,WithLp.ofLp_toLp]
  simp_rw [exp_sum_nat_counts]
  exact finiteConfigurations_joint_generating μ S hS
    (fun j => Complex.exp ((t j : ℂ)*Complex.I)) (fun j => by simp [Complex.norm_exp])
/-- Exact law of the full anonymous superposition, including zero intensities. -/
theorem finiteCountingMeasure_law (μ : ι → FiniteMeasure ℝ) :
    (finiteConfigurationsLaw μ).map finiteCountingMeasure =
      (configurationLaw (∑ i, μ i)).map countingMeasure := by
  have hFinite : MeasurableSet {m : Measure Point | m univ < ⊤} :=
    measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const
  apply ProphetSecretary.Probability.randomMeasure_law_eq_of_finite_real_evaluations
    ((finiteConfigurationsLaw μ).map finiteCountingMeasure)
    ((configurationLaw (∑ i, μ i)).map countingMeasure)
  · apply (ae_map_iff measurable_finiteCountingMeasure.aemeasurable hFinite).mpr
    exact Eventually.of_forall (fun ω => by rw [finiteCountingMeasure_univ]; exact ENNReal.natCast_lt_top _)
  · apply (ae_map_iff measurable_countingMeasure.aemeasurable hFinite).mpr
    exact Eventually.of_forall (fun ω => by rw [countingMeasure_univ]; exact ENNReal.natCast_lt_top _)
  · intro I
    have hEval : Measurable (fun m : Measure Point => fun S : I => m.real S.1.1) :=
      measurable_pi_lambda _ (fun S => (Measure.measurable_coe S.1.2).ennreal_toReal)
    rw [Measure.map_map hEval measurable_finiteCountingMeasure,Measure.map_map hEval measurable_countingMeasure]
    have hs (ω : ι → Configuration) (S : I) :
        (finiteCountingMeasure ω).real S.1.1 = ((∑ i, pointCount S.1.1 (ω i) : ℕ) : ℝ) := by
      unfold finiteCountingMeasure Measure.real
      simp only [Measure.coe_finsetSum,Finset.sum_apply,countingMeasure_eq_pointCount S.1.2,
        ← Nat.cast_sum,ENNReal.toReal_natCast]
    have ht (ω : Configuration) (S : I) :
        (countingMeasure ω).real S.1.1 = (pointCount S.1.1 ω : ℝ) := by
      change (countingMeasure ω S.1.1).toReal = _
      rw [countingMeasure_eq_pointCount S.1.2,ENNReal.toReal_natCast]
    simpa only [Function.comp_def,hs,ht] using finiteConfigurations_counts_joint_law μ
      (fun S : I => S.1.1) (fun S => S.1.2)
end ProphetSecretary.Limiting
