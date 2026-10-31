import ProphetSecretary.Model.EmpiricalTotalization

/-!
# Measurable empirical benchmarks

A fresh uniform sample index for every identity realizes the product empirical law.
This gives joint measurability of its expected maximum without an assumed kernel or
an appeal to continuity of the optimal stopping value.
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def empiricalIndexLaw (k : ℕ) : Measure (Fin k) :=
  (k : ℝ≥0∞)⁻¹ • ∑ j : Fin k, Measure.dirac j

instance empiricalIndexLaw_probability : IsProbabilityMeasure (empiricalIndexLaw k) := by
  constructor
  simp only [empiricalIndexLaw, Measure.smul_apply]
  simp
  exact ENNReal.inv_mul_cancel (a := (k : ℝ≥0∞)) (by exact_mod_cast (NeZero.ne k)) (by simp)

omit [NeZero k] in
lemma empiricalIndex_measurePreserving (v : Fin k → ℝ) :
    MeasurePreserving v (empiricalIndexLaw k) (empiricalLaw v) := by
  have hv : Measurable v := measurable_of_finite _
  refine ⟨hv, ?_⟩
  simp only [empiricalIndexLaw, empiricalLaw, Measure.map_smul,
    Measure.map_finset_sum' hv.aemeasurable, Measure.map_dirac' hv]

noncomputable def empiricalIndicesLaw (n k : ℕ) : Measure (Fin n → Fin k) :=
  Measure.pi (fun _ : Fin n => empiricalIndexLaw k)

instance empiricalIndicesLaw_probability : IsProbabilityMeasure (empiricalIndicesLaw n k) := by
  unfold empiricalIndicesLaw
  infer_instance

lemma totalEmpiricalValues_measurePreserving (y : Reservoir n k) :
    MeasurePreserving (fun a : Fin n → Fin k => fun i => max 0 (y i (a i)))
      (empiricalIndicesLaw n k) (totalEmpiricalInstance y).valuesLaw :=
  measurePreserving_pi _ _ (fun i => empiricalIndex_measurePreserving (fun j => max 0 (y i j)))

lemma totalEmpiricalInstance_expectedMaximum_eq (y : Reservoir n k) :
    (totalEmpiricalInstance y).expectedMaximum =
      ∫ a : Fin n → Fin k, Instance.maximum (fun i => max 0 (y i (a i))) ∂empiricalIndicesLaw n k := by
  have hp := totalEmpiricalValues_measurePreserving y
  have h := integral_map (μ := empiricalIndicesLaw n k) hp.measurable.aemeasurable Instance.measurable_maximum.aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h

/-- The empirical expected maximum is measurable jointly in all training entries. -/
lemma measurable_totalEmpirical_expectedMaximum {Ω : Type*} [MeasurableSpace Ω]
    {y : Ω → Reservoir n k} (hy : ∀ i j, Measurable fun ω => y ω i j) :
    Measurable fun ω => (totalEmpiricalInstance (y ω)).expectedMaximum := by
  have hf : Measurable (fun z : Ω × (Fin n → Fin k) =>
      Instance.maximum (fun i => max 0 (y z.1 i (z.2 i)))) := by
    apply measurable_from_prod_countable_left
    intro a
    apply Instance.measurable_maximum.comp
    exact measurable_pi_lambda _ (fun i => measurable_const.max (hy i (a i)))
  have hm := (hf.stronglyMeasurable.integral_prod_right' (ν := empiricalIndicesLaw n k)).measurable
  convert hm using 1
  funext ω
  exact totalEmpiricalInstance_expectedMaximum_eq (y ω)

lemma measurable_totalEmpirical_totalFirstMoment {Ω : Type*} [MeasurableSpace Ω]
    {y : Ω → Reservoir n k} (hy : ∀ i j, Measurable fun ω => y ω i j) :
    Measurable fun ω => (totalEmpiricalInstance (y ω)).totalFirstMoment := by
  change Measurable fun ω => ∑ i : Fin n, ∫ x, x ∂(totalEmpiricalInstance (y ω)).law i
  apply Finset.measurable_sum
  intro i _
  have hs : Measurable (fun ω : Ω => (k : ℝ)⁻¹ * ∑ j : Fin k, max 0 (y ω i j)) :=
    (Finset.measurable_sum _ (fun j _ => measurable_const.max (hy i j))).const_mul _
  convert hs using 1
  funext ω
  exact totalEmpiricalInstance_integral (y ω) i id

end ProphetSecretary.Model
