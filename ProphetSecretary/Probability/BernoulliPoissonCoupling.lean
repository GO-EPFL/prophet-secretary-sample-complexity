import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Measure.Prod

/-!
# A coupling of a Bernoulli count and a Poisson count

At rate p≤1, the two counts agree except on mass p(1−exp(−p)).
This is the count component of a marked rare-offer approximation.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Probability

noncomputable def bernoulliPoissonCoupling (p : unitInterval) : Measure (ℕ × ℕ) :=
  ENNReal.ofReal (1-(p:ℝ)) • Measure.dirac (0,0) +
    ENNReal.ofReal ((p:ℝ)-1+Real.exp (-(p:ℝ))) • Measure.dirac (1,0) +
      ((poissonMeasure (unitInterval.toNNReal p)).restrict ({0}ᶜ)).map (fun n => (1,n))

lemma poisson_zero_mass (p : unitInterval) :
    poissonMeasure (unitInterval.toNNReal p) {0} = ENNReal.ofReal (Real.exp (-(p:ℝ))) := by
  rw [poissonMeasure_singleton]
  simp [unitInterval.coe_toNNReal]

lemma bernoulliPoisson_extra_nonneg (p : unitInterval) :
    0 ≤ (p:ℝ)-1+Real.exp (-(p:ℝ)) := by
  have h := Real.add_one_le_exp (-(p:ℝ))
  linarith

lemma bernoulliPoissonCoupling_snd (p : unitInterval) :
    (bernoulliPoissonCoupling p).map Prod.snd = poissonMeasure (unitInterval.toNNReal p) := by
  have hc : ENNReal.ofReal (1-(p:ℝ)) +
      ENNReal.ofReal ((p:ℝ)-1+Real.exp (-(p:ℝ))) =
      ENNReal.ofReal (Real.exp (-(p:ℝ))) := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr p.2.2) (bernoulliPoisson_extra_nonneg p)]
    congr 1
    ring
  unfold bernoulliPoissonCoupling
  rw [Measure.map_add _ _ measurable_snd,Measure.map_add _ _ measurable_snd]
  simp only [Measure.map_smul,Measure.map_dirac]
  rw [Measure.map_map measurable_snd (by fun_prop)]
  change ENNReal.ofReal (1-(p:ℝ)) • Measure.dirac 0 +
    ENNReal.ofReal ((p:ℝ)-1+Real.exp (-(p:ℝ))) • Measure.dirac 0 +
      Measure.map id ((poissonMeasure (unitInterval.toNNReal p)).restrict {0}ᶜ) = _
  rw [Measure.map_id,← add_smul,hc,← poisson_zero_mass,← Measure.restrict_singleton]
  exact Measure.restrict_add_restrict_compl (measurableSet_singleton 0)

instance bernoulliPoissonCoupling_probability (p : unitInterval) :
    IsProbabilityMeasure (bernoulliPoissonCoupling p) := by
  constructor
  have h := congrArg (fun μ : Measure ℕ => μ univ) (bernoulliPoissonCoupling_snd p)
  simpa only [Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ,measure_univ] using h

lemma bernoulliPoissonCoupling_fst (p : unitInterval) :
    (bernoulliPoissonCoupling p).map Prod.fst = bernoulliMeasure (1:ℕ) 0 p := by
  have htail : (poissonMeasure (unitInterval.toNNReal p)) ({0}ᶜ) =
      1-ENNReal.ofReal (Real.exp (-(p:ℝ))) := by
    rw [measure_compl (measurableSet_singleton 0) (by finiteness),measure_univ,poisson_zero_mass]
  have he : 0 ≤ Real.exp (-(p:ℝ)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(p:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr p.2.1)
  have hc : ENNReal.ofReal ((p:ℝ)-1+Real.exp (-(p:ℝ))) +
      (1-ENNReal.ofReal (Real.exp (-(p:ℝ)))) = ENNReal.ofReal (p:ℝ) := by
    rw [← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1 he,
      ← ENNReal.ofReal_add (bernoulliPoisson_extra_nonneg p) (sub_nonneg.mpr he1)]
    congr 1
    ring
  unfold bernoulliPoissonCoupling
  rw [Measure.map_add _ _ measurable_fst,Measure.map_add _ _ measurable_fst]
  simp only [Measure.map_smul,Measure.map_dirac]
  rw [Measure.map_map measurable_fst (by fun_prop)]
  change ENNReal.ofReal (1-(p:ℝ)) • Measure.dirac 0 +
    ENNReal.ofReal ((p:ℝ)-1+Real.exp (-(p:ℝ))) • Measure.dirac 1 +
      Measure.map (fun _ : ℕ => (1:ℕ)) ((poissonMeasure (unitInterval.toNNReal p)).restrict {0}ᶜ) = _
  rw [Measure.map_const,Measure.restrict_apply_univ,htail,add_assoc,← add_smul,hc,add_comm]
  unfold bernoulliMeasure
  congr 1
  · rw [← unitInterval.coe_toNNReal p,ENNReal.ofReal_coe_nnreal,Measure.coe_nnreal_smul]
  · congr 1
    rw [← unitInterval.coe_symm_eq p,← unitInterval.coe_toNNReal (unitInterval.symm p),ENNReal.ofReal_coe_nnreal]
lemma bernoulliPoissonCoupling_diagonal (p : unitInterval) :
    (bernoulliPoissonCoupling p) {z | z.1=z.2} =
      ENNReal.ofReal (1-(p:ℝ)) + ENNReal.ofReal (Real.exp (-(p:ℝ))*(p:ℝ)) := by
  have hpre : (fun n : ℕ => (1,n)) ⁻¹' {z : ℕ × ℕ | z.1=z.2} = {1} := by
    ext n
    simp [eq_comm]
  have hInt : ({1} : Set ℕ) ∩ {0}ᶜ = {1} := by ext n; simp_all
  unfold bernoulliPoissonCoupling
  rw [Measure.add_apply,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    Measure.map_apply (by fun_prop) (measurableSet_eq_fun measurable_fst measurable_snd),hpre,
    Measure.restrict_apply (measurableSet_singleton 1),hInt,poissonMeasure_singleton]
  simp [Measure.dirac_apply,unitInterval.coe_toNNReal]

lemma bernoulliPoissonCoupling_mismatch (p : unitInterval) :
    (bernoulliPoissonCoupling p).real {z | z.1≠z.2} =
      (p:ℝ)*(1-Real.exp (-(p:ℝ))) := by
  have hD : MeasurableSet {z : ℕ × ℕ | z.1=z.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hC : {z : ℕ × ℕ | z.1≠z.2} = {z : ℕ × ℕ | z.1=z.2}ᶜ := rfl
  rw [hC,measureReal_compl hD,probReal_univ,Measure.real,
    bernoulliPoissonCoupling_diagonal,
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_ofReal (sub_nonneg.mpr p.2.2),ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le p.2.1)]
  ring

lemma bernoulliPoissonCoupling_mismatch_le (p : unitInterval) :
    (bernoulliPoissonCoupling p).real {z | z.1≠z.2} ≤ (p:ℝ)^2 := by
  rw [bernoulliPoissonCoupling_mismatch]
  have he := Real.add_one_le_exp (-(p:ℝ))
  nlinarith [mul_le_mul_of_nonneg_left (show 1-Real.exp (-(p:ℝ)) ≤ (p:ℝ) by linarith) p.2.1]
end ProphetSecretary.Probability
