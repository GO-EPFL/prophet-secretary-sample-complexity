import ProphetSecretary.Statistics.NormalizedGameKernel
import ProphetSecretary.Statistics.Hoeffding.EmpiricalKernel
import ProphetSecretary.Statistics.EmpiricalMaximumVariance

/-!
# The frozen policy and the product-empirical scalar gap

On valid training arrays the original kernel's empirical mean is exactly
the frozen policy's empirical scalar objective minus the empirical benchmark.
It is bounded above by the empirical optimum at that same fixed scalar.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal

namespace ProphetSecretary.Model
open ProphetSecretary.Statistics.Hoeffding

variable {n k : ℕ} [NeZero k]

lemma RandomizedPolicy.empiricalMean_normalizedGameKernel (π : RandomizedPolicy n)
    {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) (y : (Fin n × Fin k) → ℝ)
    (hy : ∀ q, y q ∈ Icc (0 : ℝ) 1) :
    empiricalMean (π.normalizedGameKernel lam) y =
      π.scalarObjective (totalEmpiricalInstance (reservoirCoordinates.symm y)) lam (1-lam) -
        optimalCompetitiveRatio*(lam*empiricalExpectedMaximum y+(1-lam)) := by
  let E := totalEmpiricalInstance (reservoirCoordinates.symm y)
  have hcap : ∀ i, ∀ᵐ a ∂E.law i, a ≤ 1 :=
    totalEmpiricalInstance_bounded _ zero_le_one (fun i j => (hy (i,j)).2)
  have hp := totalEmpiricalValues_measurePreserving (reservoirCoordinates.symm y)
  have hm := integral_map (μ := empiricalIndicesLaw n k) hp.measurable.aemeasurable
    (π.measurable_normalizedGameKernel lam).aestronglyMeasurable
  rw [hp.map_eq] at hm
  have heq : empiricalMean (π.normalizedGameKernel lam) y =
      ∫ x, π.normalizedGameKernel lam x ∂E.valuesLaw := by
    change (∫ a : Fin n → Fin k, π.normalizedGameKernel lam (fun i => y (i,a i))
      ∂empiricalIndicesLaw n k) = _
    rw [hm]
    apply integral_congr_ae
    exact Eventually.of_forall fun a => congrArg (π.normalizedGameKernel lam) (by
      funext i
      exact (max_eq_right (hy (i,a i)).1).symm)
  rw [heq,π.integral_normalizedGameKernel E hcap hlam]
  rfl

lemma RandomizedPolicy.empiricalMean_normalizedGameKernel_le_gap (π : RandomizedPolicy n)
    {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) (y : (Fin n × Fin k) → ℝ)
    (hy : ∀ q, y q ∈ Icc (0 : ℝ) 1) :
    empiricalMean (π.normalizedGameKernel lam) y ≤
      normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) lam := by
  rw [π.empiricalMean_normalizedGameKernel hlam y hy]
  let E := totalEmpiricalInstance (reservoirCoordinates.symm y)
  have hcap : ∀ i, ∀ᵐ a ∂E.law i, a ≤ 1 :=
    totalEmpiricalInstance_bounded _ zero_le_one (fun i j => (hy (i,j)).2)
  exact sub_le_sub_right (scalarObjective_le_optimal π E
    (E.integrable_maximum_of_bounded hcap) hlam.1.le (sub_nonneg.mpr hlam.2)) _

lemma Instance.empiricalMean_normalizedGameKernel_le_gap_ae (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) (π : RandomizedPolicy n)
    {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) :
    ∀ᵐ y ∂P.trainingCoordinateLaw k, empiricalMean (π.normalizedGameKernel lam) y ≤
      normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) lam := by
  have hNonnegative : ∀ᵐ y ∂P.trainingCoordinateLaw k, ∀ q, 0 ≤ y q := by
    apply ae_all_iff.mpr
    intro q
    exact (measurePreserving_eval (fun q : Fin n × Fin k => P.law q.1) q).quasiMeasurePreserving.ae
      (P.nonnegative q.1)
  filter_upwards [hNonnegative,P.training_array_cap_ae (k := k) hcap] with y hy hycap
  exact π.empiricalMean_normalizedGameKernel_le_gap hlam y (fun q => ⟨hy q,hycap q⟩)

end ProphetSecretary.Model
