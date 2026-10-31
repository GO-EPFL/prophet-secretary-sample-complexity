import ProphetSecretary.Model.OuterTaggedMaximum
import ProphetSecretary.Probability.TaggedCDFUniform

/-!
# The uniform CDF score of an actual tagged maximum

At numerical value x, the tagged CDF is the finite product of the affine factors
P(X_i<x)+u P(X_i=x). Continuous variation of u fills the whole numerical CDF jump,
including zero atoms and simultaneous numerical ties among variables.
Paper correspondence: G and the uniform transform in `upouter:beta`.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model.Instance
open ProphetSecretary.Probability
variable {n : ℕ}

lemma taggedFailureProbability_affine (P : Instance n) (i : Fin n) (x u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    1-P.taggedExceedanceProbability (x,u) i=(P.law i).real (Iio x)+u*(P.law i).real {x} := by
  let μ := (P.law i).prod uniformClock
  have hCompl : 1-P.taggedExceedanceProbability (x,u) i=μ.real {z | ¬taggedAbove (x,u) z} := by
    simpa only [μ,taggedExceedanceProbability,Set.compl_setOf] using
      (probReal_compl_eq_one_sub (μ:=μ) (measurableSet_taggedAbove_fixed (x,u))).symm
  have hSet : {z : ℝ × ℝ | ¬taggedAbove (x,u) z}=(Iio x×ˢSet.univ)∪({x}×ˢIic u) := by
    ext z
    change ¬taggedAbove (x,u) z ↔ _
    rw [taggedAbove_iff_lex_lt,not_lt,Prod.Lex.le_iff]
    simp only [Set.mem_union,Set.mem_prod,Set.mem_Iio,Set.mem_univ,and_true,Set.mem_singleton_iff,Set.mem_Iic]
    rfl
  have hDisj : Disjoint (Iio x×ˢ(Set.univ : Set ℝ)) ({x}×ˢIic u) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨hz,_⟩ ⟨he,_⟩
    exact (ne_of_lt hz) (Set.mem_singleton_iff.mp he)
  have hU : uniformClock.real (Iic u)=u := by
    rw [uniformClock_lowerCDF,min_eq_left hu.2,max_eq_left hu.1]
  rw [hCompl,hSet,measureReal_union hDisj ((measurableSet_singleton x).prod measurableSet_Iic)]
  have hRect : μ.real (Iio x×ˢ(Set.univ : Set ℝ))+μ.real ({x}×ˢIic u)=
      (P.law i).real (Iio x)+(P.law i).real {x}*uniformClock.real (Iic u) := by
    simp only [μ,Measure.real,Measure.prod_prod,ENNReal.toReal_mul,measure_univ,mul_one]
  rw [hRect,hU]
  ring

lemma outerTaggedMaximum_cdf_affine (P : Instance n) (hn : 0<n) (x u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    orderCDF (P.outerTaggedMaximumLaw hn) (toLex (x,u))=
      ∏ i : Fin n, ((P.law i).real (Iio x)+u*(P.law i).real {x}) := by
  rw [P.outerTaggedMaximum_cdf_eq_void hn]
  unfold taggedVoidProbability
  exact Finset.prod_congr rfl fun i _ => P.taggedFailureProbability_affine i x u hu

lemma outerTaggedMaximum_cdf_vertical_continuous (P : Instance n) (hn : 0<n) (x : ℝ) :
    ContinuousOn (fun u : ℝ => orderCDF (P.outerTaggedMaximumLaw hn) (toLex (x,u))) (Icc (0:ℝ) 1) := by
  have hPoly : Continuous (fun u : ℝ => ∏ i : Fin n, ((P.law i).real (Iio x)+u*(P.law i).real {x})) :=
    continuous_finsetProd Finset.univ (fun i _ => continuous_const.add (continuous_id.mul_const _))
  exact hPoly.continuousOn.congr (fun u hu => P.outerTaggedMaximum_cdf_affine hn x u hu)

/-- The actual complete offer/tag vector has a uniform tagged-maximum CDF score.
The score is analytical; the cutoff algorithm itself uses only observed tags/values. -/
theorem outerTaggedMaximum_score_measurePreserving (P : Instance n) (hn : 0<n) :
    MeasurePreserving (fun z : Fin n → ℝ × ℝ => P.taggedVoidProbability (ofLex (outerTaggedMaximum hn z)))
      P.taggedValuesLaw uniformClock := by
  have hUniform := tagged_orderCDF_uniform (P.outerTaggedMaximumLaw hn)
    (P.outerTaggedMaximum_tag_mem_open_unit hn) (P.outerTaggedMaximum_cdf_vertical_continuous hn)
  have hMax : MeasurePreserving (outerTaggedMaximum hn) P.taggedValuesLaw (P.outerTaggedMaximumLaw hn) :=
    ⟨measurable_outerTaggedMaximum hn,rfl⟩
  have hEq : (fun z : Fin n → ℝ × ℝ => orderCDF (P.outerTaggedMaximumLaw hn) (outerTaggedMaximum hn z))=
      (fun z => P.taggedVoidProbability (ofLex (outerTaggedMaximum hn z))) :=
    funext (fun z => P.outerTaggedMaximum_cdf_eq_void hn (outerTaggedMaximum hn z))
  rw [←hEq]
  simpa only [Function.comp_def] using hUniform.comp hMax

end ProphetSecretary.Model.Instance
