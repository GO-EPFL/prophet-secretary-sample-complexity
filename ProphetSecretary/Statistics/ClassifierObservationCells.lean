import ProphetSecretary.Statistics.ClassifierResponseBounds

/-!
# Actual finite classifier cells

A coded in-grid cell is a singleton preliminary sample array. Its invalid mass
is therefore either the whole cell mass or zero. Off-grid cells have zero
probability under the actual finite-support product training laws.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Analysis

lemma finiteObservationCode_eq_some_iff {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] (D : Finset A) (y : {a : A // a∈D}) (a : A) :
    finiteObservationCode D a=some y ↔ a=y.val := by
  change a∈(finiteObservationCode D) ⁻¹' {some y} ↔ a=y.val
  rw [finiteObservationCode_preimage_some]
  rfl

lemma classifierCell_invalid_mass {n h : ℕ} (P : Instance n) (G : Finset ℝ)
    (y : {a : (Fin n × Fin h) → ℝ // a∈preliminaryGrid n h G}) (Sstar S : ℝ) :
    (P.trainingCoordinateLaw h).real {a | finiteObservationCode (preliminaryGrid n h G) a=some y ∧
      a∈invalidFirstMomentClass Sstar S}=
      if y.val∈invalidFirstMomentClass Sstar S then
        (P.trainingCoordinateLaw h).real {a | finiteObservationCode (preliminaryGrid n h G) a=some y} else 0 := by
  simp_rw [finiteObservationCode_eq_some_iff]
  by_cases hy : y.val∈invalidFirstMomentClass Sstar S
  · rw [if_pos hy]
    congr 1
    ext a
    simp only [mem_setOf_eq]
    exact ⟨And.left,fun h => ⟨h,h ▸ hy⟩⟩
  · rw [if_neg hy]
    have hE : {a | a=y.val ∧ a∈invalidFirstMomentClass (n:=n) (h:=h) Sstar S}=∅ := by
      ext a
      simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
      exact fun h => hy (h.1 ▸ h.2)
    rw [hE,measureReal_empty]

lemma classifierCell_off_grid_mass {n h : ℕ} (P : Instance n) (G : Finset ℝ)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) :
    (P.trainingCoordinateLaw h).real {a | finiteObservationCode (preliminaryGrid n h G) a=none}=0 := by
  have hNull := ae_iff.mp (trainingCoordinateLaw_grid_support P G h hG)
  have hE : {a | finiteObservationCode (preliminaryGrid n h G) a=none}=
      (preliminaryGrid n h G : Set ((Fin n × Fin h) → ℝ))ᶜ := by
    exact finiteObservationCode_preimage_none _
  have hNull' : (P.trainingCoordinateLaw h)
      (preliminaryGrid n h G : Set ((Fin n × Fin h) → ℝ))ᶜ=0 := hNull
  rw [Measure.real,hE,hNull',ENNReal.toReal_zero]

lemma validClassifier_low {n h : ℕ} (y : (Fin n × Fin h) → ℝ) (Sstar S : ℝ)
    (hy : y∉invalidFirstMomentClass Sstar S) (hLow : selectLowFirstMoment Sstar y=true) : S≤3*Sstar := by
  by_contra h
  exact hy (Or.inl ⟨hLow,lt_of_not_ge h⟩)

lemma validClassifier_high {n h : ℕ} (y : (Fin n × Fin h) → ℝ) (Sstar S : ℝ)
    (hy : y∉invalidFirstMomentClass Sstar S) (hHigh : selectLowFirstMoment Sstar y=false) : Sstar≤S := by
  by_contra h
  exact hy (Or.inr ⟨hHigh,lt_of_not_ge h⟩)

end ProphetSecretary.Statistics
