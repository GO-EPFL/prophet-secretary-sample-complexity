import ProphetSecretary.Limiting.CountableCutoffGenerating

/-!
# Finite evaluation distributions of the cutoff process

Equality of the generating tests gives the full joint law of real count
vectors, for arbitrary overlapping measurable regions.
-/

open MeasureTheory ProbabilityTheory Set Filter Complex
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting

lemma exp_sum_nat_counts {ι : Type*} [Fintype ι] (N : ι → ℕ) (t : ι → ℝ) :
    Complex.exp ((((∑ i, (N i : ℝ)*t i) : ℝ) : ℂ)*Complex.I) =
      ∏ i, Complex.exp ((t i : ℂ)*Complex.I)^N i := by
  rw [Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

namespace CountableInstance

variable (B : CountableInstance) {ι : Type*} [Fintype ι]

theorem cutoff_counts_real_joint_law {b : ℝ} (hb : (B.terminal : ℝ) < b)
    (S : ι → Set Point) (hS : ∀ i, MeasurableSet (S i)) :
    B.bandConfigurationsLaw.map (fun ω i => (bandPointCount (S i ∩ (univ ×ˢ Ioi b)) ω : ℝ)) =
      (configurationLaw (B.intensityAbove b hb)).map (fun ω i => (pointCount (S i) ω : ℝ)) := by
  let R := fun i => S i ∩ (univ ×ˢ Ioi b)
  let f : BandConfigurations → (ι → ℝ) := fun ω i => (bandPointCount (R i) ω : ℝ)
  let h : Configuration → (ι → ℝ) := fun ω i => (pointCount (S i) ω : ℝ)
  have hf : Measurable f := measurable_pi_lambda _ (fun i =>
    (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp
      (measurable_bandPointCount ((hS i).inter (MeasurableSet.univ.prod measurableSet_Ioi))))
  have hh : Measurable h := measurable_pi_lambda _ (fun i =>
    (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp (measurable_pointCount (hS i)))
  let e := MeasurableEquiv.toLp 2 (ι → ℝ)
  change B.bandConfigurationsLaw.map f = (configurationLaw (B.intensityAbove b hb)).map h
  apply MeasurableEquiv.map_measurableEquiv_injective e
  rw [Measure.map_map e.measurable hf,Measure.map_map e.measurable hh]
  apply Measure.ext_of_charFun
  funext t
  have hfLp := e.measurable.comp hf
  have hhLp := e.measurable.comp hh
  rw [charFun_apply,charFun_apply,integral_map hfLp.aemeasurable (by fun_prop),
    integral_map hhLp.aemeasurable (by fun_prop)]
  simp only [PiLp.inner_apply,Real.inner_apply,f,h]
  dsimp only [Function.comp_def,e,MeasurableEquiv.coe_toLp,WithLp.ofLp_toLp]
  simp_rw [exp_sum_nat_counts]
  exact B.cutoff_counts_joint_generating hb S hS
    (fun i => Complex.exp ((t i : ℂ)*Complex.I)) (fun i => by simp [Complex.norm_exp])

end CountableInstance
end ProphetSecretary.Limiting
