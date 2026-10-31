import ProphetSecretary.Probability.FiniteSimplexLaw

/-!
# An actual law supported by a finite real alphabet

The singleton masses form a probability vector on the alphabet. Mapping
its finite probability law back to real values recovers the original law.
No positive-mass assumption is required at any alphabet point.
-/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace ProphetSecretary.Probability

lemma finiteSupport_weights_simplex (μ : Measure ℝ) [IsProbabilityMeasure μ] (G : Finset ℝ)
    (hG : ∀ᵐ x ∂μ, x∈G) : (fun a : G => μ.real {a.val})∈stdSimplex ℝ G := by
  refine ⟨fun _ => measureReal_nonneg,?_⟩
  have hEq : (G : Set ℝ)=ᵐ[μ] Set.univ := by
    filter_upwards [hG] with x hx
    exact propext ⟨fun _ => Set.mem_univ x,fun _ => hx⟩
  have hMass : μ.real (G : Set ℝ)=1 := (measureReal_congr hEq).trans probReal_univ
  have hSum := sum_measureReal_singleton (μ:=μ) G
  rw [hMass] at hSum
  exact (Finset.sum_coe_sort G (fun x : ℝ => μ.real {x})).trans hSum

lemma finiteSupport_map_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (G : Finset ℝ)
    (hG : ∀ᵐ x ∂μ, x∈G) :
    (finiteSimplexLaw (fun a : G => μ.real {a.val}) (finiteSupport_weights_simplex μ G hG)).map
      (fun a : G => a.val) = μ := by
  have hAtomic := Measure.ae_mem_finset_iff.mp hG
  conv_rhs => rw [hAtomic]
  unfold finiteSimplexLaw
  rw [Measure.map_finset_sum' measurable_subtype_coe.aemeasurable]
  simp only [Measure.map_smul,Measure.map_dirac' measurable_subtype_coe]
  conv_rhs => rw [← Finset.sum_coe_sort G (fun x : ℝ => μ {x} • Measure.dirac x)]
  apply Finset.sum_congr rfl
  intro a _
  have he : (simplexNNWeight (fun a : G => μ.real {a.val}) (finiteSupport_weights_simplex μ G hG) a : ℝ≥0∞)=μ {a.val} := by
    rw [← ENNReal.ofReal_coe_nnreal,coe_simplexNNWeight,measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact congrArg (fun c : ℝ≥0∞ => c • Measure.dirac a.val) he

end ProphetSecretary.Probability
