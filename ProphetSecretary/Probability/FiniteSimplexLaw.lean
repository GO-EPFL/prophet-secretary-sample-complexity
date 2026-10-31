import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual finite probability laws and simplex weights

The finite minimax weights define a probability measure, and conversely the
singleton masses of an actual finite probability law form a simplex vector.
The expectation identity is for the constructed measure itself.
-/

open MeasureTheory Set
open scoped Classical BigOperators NNReal

namespace ProphetSecretary.Probability

variable {Θ : Type*} [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

noncomputable def simplexNNWeight (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) (θ : Θ) : ℝ≥0 :=
  ⟨p θ,hp.1 θ⟩

omit [MeasurableSpace Θ] [MeasurableSingletonClass Θ] in
lemma coe_simplexNNWeight (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) (θ : Θ) :
    (simplexNNWeight p hp θ : ℝ) = p θ := rfl

noncomputable def finiteSimplexLaw (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) : Measure Θ :=
  ∑ θ, simplexNNWeight p hp θ • Measure.dirac θ

instance finiteSimplexLaw_probability (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) :
    IsProbabilityMeasure (finiteSimplexLaw p hp) := by
  constructor
  simp only [finiteSimplexLaw,Measure.finsetSum_apply,Measure.smul_apply,measure_univ,ENNReal.smul_one]
  have hSum : (∑ θ, simplexNNWeight p hp θ) = 1 := by
    apply NNReal.eq
    simpa only [NNReal.coe_sum,coe_simplexNNWeight,NNReal.coe_one] using hp.2
  exact_mod_cast hSum

lemma finiteProbability_singletons_simplex (μ : Measure Θ) [IsProbabilityMeasure μ] :
    (fun θ => μ.real {θ})∈stdSimplex ℝ Θ := by
  refine ⟨fun _ => measureReal_nonneg,?_⟩
  have h := sum_measureReal_singleton (μ := μ) (Finset.univ : Finset Θ)
  simpa only [Finset.coe_univ,probReal_univ] using h

lemma integral_finiteSimplexLaw (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) (f : Θ → ℝ) :
    (∫ θ, f θ ∂finiteSimplexLaw p hp) = ∑ θ, p θ*f θ := by
  have hI (θ : Θ) : Integrable f (Measure.dirac θ) := integrable_dirac (by finiteness)
  unfold finiteSimplexLaw
  rw [integral_finsetSum_measure (fun θ _ => (hI θ).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure,integral_dirac,NNReal.smul_def,smul_eq_mul,coe_simplexNNWeight]

lemma finiteSimplexLaw_real_singleton (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) (θ : Θ) :
    (finiteSimplexLaw p hp).real {θ} = p θ := by
  have hMean := integral_finiteSimplexLaw p hp (fun a => if a=θ then (1 : ℝ) else 0)
  have hValue : (∫ a, (if a=θ then (1 : ℝ) else 0) ∂finiteSimplexLaw p hp) = p θ := by
    simpa using hMean
  have hMass : (∫ a, (if a=θ then (1 : ℝ) else 0) ∂finiteSimplexLaw p hp) =
      (finiteSimplexLaw p hp).real {θ} := by
    simpa only [Set.indicator_apply,Set.mem_singleton_iff,smul_eq_mul,mul_one] using
      integral_indicator_const (μ := finiteSimplexLaw p hp) (1 : ℝ) (measurableSet_singleton θ)
  exact hMass.symm.trans hValue

lemma integral_finiteProbability (μ : Measure Θ) [IsProbabilityMeasure μ] (f : Θ → ℝ) :
    (∫ θ, f θ ∂μ) = ∑ θ, μ.real {θ}*f θ := by
  simpa only [smul_eq_mul] using integral_fintype (Integrable.of_finite : Integrable f μ)

end ProphetSecretary.Probability
