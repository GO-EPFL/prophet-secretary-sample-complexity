import ProphetSecretary.Limiting.HybridDesignLossComparison

/-!
# Measurable integrable clock-only continuation errors

The finite design and the actual hybrid continuation are evaluated on the
same original/anonymous clocks. Their values use only unseen identities and
elapsed time. Under the actual uniform clock law the absolute error is bounded
by the sum of the initial finite design value and the hybrid cap bound.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n q N : ℕ}

lemma FiniteIntensityHybridInstance.measurable_finiteDesignContinuationError
    (B : FiniteIntensityHybridInstance n) (Q : Model.Instance (n+q))
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (k : Fin (n+N)) :
    Measurable (fun u : Fin (n+q+N) → ℝ => B.finiteDesignContinuationError Q w c u k) := by
  let e := (HybridZeroSimulation.keepEmbedding n q N).toEmbedding
  have hD : Measurable (fun u : Fin (n+q+N) → ℝ =>
      (Q.appendZeros N).continuationAtArrival w c (fun _ => 0) u (e k)) :=
    (Q.appendZeros N).measurable_continuationAtArrival (Q.appendZeros_integrable_maximum N hQ) hw hc
      (fun _ => measurable_const) (fun i => measurable_pi_apply i) (e k)
  have hA : Measurable (fun u : Fin (n+q+N) → ℝ => B.finiteContinuationAtArrival w c (fun _ => 0) (u ∘ e) k) :=
    B.measurable_finiteContinuationAtArrival hw.le hc (fun _ => measurable_const)
      (fun i => measurable_pi_apply (e i)) k
  exact continuous_abs.measurable.comp (hD.sub hA)

lemma FiniteIntensityHybridInstance.integrable_finiteDesignContinuationError
    (B : FiniteIntensityHybridInstance n) (Q : Model.Instance (n+q))
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (k : Fin (n+N)) :
    Integrable (fun u : Fin (n+q+N) → ℝ => B.finiteDesignContinuationError Q w c u k)
      (Model.Instance.clocksLaw (n+q+N)) := by
  let e := (HybridZeroSimulation.keepEmbedding n q N).toEmbedding
  let K := Model.optimalScalarValue Q w c+(2*w*(B.cap : ℝ)+c)
  apply Integrable.of_bound (B.measurable_finiteDesignContinuationError Q hQ hw hc k).aestronglyMeasurable K
  filter_upwards [Model.Instance.clocks_mem_unitInterval (n := n+q+N)] with u hu
  have hD0 := (Q.appendZeros N).continuationAtArrival_nonnegative
    (Q.appendZeros_integrable_maximum N hQ) hw.le hc (fun _ => 0) u (e k)
  have hD1 := (Q.appendZeros N).continuationAtArrival_le_initial
    (Q.appendZeros_integrable_maximum N hQ) hw.le hc (fun _ => 0) u (e k) (hu (e k)).1
  rw [Q.optimalScalarValue_appendZeros N hQ hw.le hc] at hD1
  have hA := B.finiteContinuationAtArrival_bounds hw hc (fun _ => 0) (u ∘ e) k (hu (e k)).1
  have hAbs : |(Q.appendZeros N).continuationAtArrival w c (fun _ => 0) u (e k)-
      B.finiteContinuationAtArrival w c (fun _ => 0) (u ∘ e) k| ≤
      (Q.appendZeros N).continuationAtArrival w c (fun _ => 0) u (e k)+
        B.finiteContinuationAtArrival w c (fun _ => 0) (u ∘ e) k :=
    abs_le.mpr ⟨by linarith only [hD0],by linarith only [hA.1]⟩
  simpa only [FiniteIntensityHybridInstance.finiteDesignContinuationError,Real.norm_eq_abs,abs_abs] using
    hAbs.trans (add_le_add hD1 hA.2)

end ProphetSecretary.Limiting
