import ProphetSecretary.Statistics.ObservableFirstMomentClassifier
import ProphetSecretary.Analysis.ClassifierRounds

/-!
# Invalid-class probability with a logarithmic preliminary sample

Low selection is valid for S≤3Sstar; high selection is valid for S≥Sstar. The
classes overlap. Consequently only one tail can cause an invalid choice for a
fixed instance, and no factor two is lost when bounding its probability.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Analysis
variable {n h : ℕ}

/-- S is used only to analyze whether the sample-based class choice is valid. -/
def invalidFirstMomentClass (Sstar S : ℝ) : Set ((Fin n × Fin h) → ℝ) :=
  {a | (selectLowFirstMoment Sstar a=true ∧ 3*Sstar<S) ∨
    (selectLowFirstMoment Sstar a=false ∧ S<Sstar)}

lemma measurableSet_invalidFirstMomentClass (Sstar S : ℝ) :
    MeasurableSet (invalidFirstMomentClass (n:=n) (h:=h) Sstar S) := by
  have hL := measurableSet_eq_fun (measurable_selectLowFirstMoment (n:=n) (h:=h) Sstar) (measurable_const (a:=true))
  have hH := measurableSet_eq_fun (measurable_selectLowFirstMoment (n:=n) (h:=h) Sstar) (measurable_const (a:=false))
  by_cases h1 : 3*Sstar<S <;> by_cases h2 : S<Sstar
  · simpa only [invalidFirstMomentClass,h1,h2,and_true,Set.union_def,Set.mem_setOf_eq] using hL.union hH
  · simpa only [invalidFirstMomentClass,h1,h2,and_true,and_false,or_false] using hL
  · simpa only [invalidFirstMomentClass,h1,h2,and_true,and_false,false_or] using hH
  · simp only [invalidFirstMomentClass,h1,h2,and_false,or_self,Set.setOf_false,MeasurableSet.empty]

/-- The source invalid-selection probability, with every constant independent of n. -/
theorem firstMomentClassifier_invalid_probability (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {m : ℕ} (hm : 2≤m)
    {Sstar : ℝ} (hS : 1≤Sstar) :
    (P.trainingCoordinateLaw (classifierRounds m)).real
      (invalidFirstMomentClass Sstar P.totalFirstMoment)≤1/(m:ℝ)^4 := by
  have hh := classifierRounds_positive hm
  have hS0 : 0≤Sstar := by linarith only [hS]
  by_cases hLow : P.totalFirstMoment<Sstar
  · have hSub : invalidFirstMomentClass (n:=n) (h:=classifierRounds m) Sstar P.totalFirstMoment⊆
        {a | selectLowFirstMoment Sstar a=false} := by
      intro a ha
      rcases ha with ⟨_,h⟩|⟨h,_⟩
      · linarith only [hLow,h,hS0]
      · exact h
    exact (measureReal_mono hSub (measure_ne_top _ _)).trans
      ((firstMomentClassifier_low_tail P hcap hh hS0 hLow.le).trans
        (classifier_upper_error_le_inverse_fourth (by omega) hS))
  · by_cases hHigh : 3*Sstar<P.totalFirstMoment
    · have hSub : invalidFirstMomentClass (n:=n) (h:=classifierRounds m) Sstar P.totalFirstMoment⊆
          {a | selectLowFirstMoment Sstar a=true} := by
        intro a ha
        rcases ha with ⟨h,_⟩|⟨_,h⟩
        · exact h
        · exact False.elim (hLow h)
      exact (measureReal_mono hSub (measure_ne_top _ _)).trans
        ((firstMomentClassifier_high_tail P hcap hh hS0 hHigh.le).trans
          (classifier_lower_error_le_inverse_fourth (by omega) hS))
    · have hE : invalidFirstMomentClass (n:=n) (h:=classifierRounds m) Sstar P.totalFirstMoment=∅ := by
        ext a
        simp only [invalidFirstMomentClass,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false,not_or,not_and]
        exact ⟨fun _ => hHigh,fun _ => hLow⟩
      rw [hE,measureReal_empty]
      positivity

end ProphetSecretary.Statistics
