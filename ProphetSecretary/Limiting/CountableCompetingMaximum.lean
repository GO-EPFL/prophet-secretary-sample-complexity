import ProphetSecretary.Limiting.CountableValueReplacementIndependence
import ProphetSecretary.Limiting.CountablePolicyBounds

/-!
# The actual maximum competing with one individual

Replacing one value by zero defines its competing maximum on the complete
world. This analytical quantity includes future offers, but is not supplied
to any policy. The actual infinite-product erasure proves independence from
the original value. Bounded countable suprema give the maximum decomposition
on every fixed replacement, without removing a zero-valued identity.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

noncomputable def competingMaximum (B : CountableInstance) (i : ℕ) (v : CompleteWorld Seed) : ℝ :=
  B.maximum (v.1,Function.update v.2.1 i 0)

lemma maximum_replaceIndividual_eq_max (B : CountableInstance) (i : ℕ) (v : ValueWorld)
    (hBound : ∀ j, candidateMaxima v j ≤ (B.cap : ℝ)) (x : ℝ) :
    B.maximum (v.1,Function.update v.2 i x)=max x (B.maximum (v.1,Function.update v.2 i 0)) := by
  let f : ℝ → ℕ → ℝ := fun z => candidateMaxima (v.1,Function.update v.2 i z)
  have hCap (z : ℝ) (j : ℕ) : f z j ≤ max (B.cap : ℝ) z := by
    by_cases hji : j=i
    · subst j
      simp only [f,candidateMaxima,Function.update_self]
      exact max_le (le_max_right _ _) (((le_max_right _ _).trans (hBound i)).trans (le_max_left _ _))
    · change max (Function.update v.2 i z j) (bandMaximum (v.1 j)) ≤ _
      rw [Function.update_of_ne hji]
      exact (hBound j).trans (le_max_left _ _)
  have hBase (z : ℝ) : (B.terminal : ℝ) ≤ max (B.cap : ℝ) z :=
    (show (B.terminal : ℝ) ≤ B.cap by exact_mod_cast B.terminal_le_cap).trans (le_max_left _ _)
  have hH (z : ℝ) : 0 ≤ max (B.cap : ℝ) z := B.cap.property.trans (le_max_left _ _)
  have hAbove (z : ℝ) (j : ℕ) : f z j ≤ B.maximum (v.1,Function.update v.2 i z) :=
    le_countableMaximum (hBase z) (hH z) (f z) (hCap z) j
  have hTerminal (z : ℝ) : (B.terminal : ℝ) ≤ B.maximum (v.1,Function.update v.2 i z) :=
    terminal_le_countableMaximum (hBase z) (hH z) (f z) (hCap z)
  have hNonnegative (z : ℝ) : 0 ≤ B.maximum (v.1,Function.update v.2 i z) :=
    B.terminal.property.trans (hTerminal z)
  have hBand (z : ℝ) (j : ℕ) : bandMaximum (v.1 j) ≤ B.maximum (v.1,Function.update v.2 i z) :=
    (le_max_right _ _).trans (hAbove z j)
  have hX : x ≤ B.maximum (v.1,Function.update v.2 i x) := by
    have h := hAbove x i
    simp only [f,candidateMaxima,Function.update_self] at h
    exact (le_max_left _ _).trans h
  have hComp : B.maximum (v.1,Function.update v.2 i 0) ≤ B.maximum (v.1,Function.update v.2 i x) := by
    apply countableMaximum_le (hTerminal x) (hNonnegative x) (f 0)
    intro j
    by_cases hji : j=i
    · subst j
      simp only [f,candidateMaxima,Function.update_self]
      exact max_le (hNonnegative x) (hBand x i)
    · have hEq : f 0 j=f x j := by
        simp only [f,candidateMaxima,Function.update_of_ne hji]
      exact hEq.trans_le (hAbove x j)
  apply le_antisymm
  · apply countableMaximum_le ((hTerminal 0).trans (le_max_right _ _)) ((hNonnegative 0).trans (le_max_right _ _)) (f x)
    intro j
    by_cases hji : j=i
    · subst j
      simp only [f,candidateMaxima,Function.update_self]
      exact max_le (le_max_left _ _) ((hBand 0 i).trans (le_max_right _ _))
    · have hEq : f x j=f 0 j := by
        simp only [f,candidateMaxima,Function.update_of_ne hji]
      exact hEq.trans_le ((hAbove 0 j).trans (le_max_right _ _))
  · exact max_le hX hComp

variable [MeasurableSpace Seed]

lemma measurable_competingMaximum (B : CountableInstance) (i : ℕ) :
    Measurable (B.competingMaximum (Seed := Seed) i) :=
  B.measurable_maximum.comp (measurable_fst.prodMk
    (((Model.measurable_eraseCoordinate i (0 : ℝ)).comp (measurable_fst.comp measurable_snd))))

theorem competingMaximum_independent_value (B : CountableInstance) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : ℕ) :
    IndepFun (B.competingMaximum i) (fun v : CompleteWorld Seed => v.2.1 i) (B.completeWorldLaw ν) := by
  have hM : Measurable (fun v : CompleteWorld Seed => B.maximum (v.1,v.2.1)) :=
    B.measurable_maximum.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact (eraseIndividualValue_independent B ν i).comp hM measurable_id

theorem maximum_replaceIndividual_eq_max_ae (B : CountableInstance) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : ℕ) :
    ∀ᵐ v ∂B.completeWorldLaw ν, ∀ x : ℝ,
      B.maximum (v.1,Function.update v.2.1 i x)=max x (B.competingMaximum i v) := by
  filter_upwards [(B.value_projection_measurePreserving ν).quasiMeasurePreserving.ae B.candidateMaxima_bounded]
    with v hv x
  exact B.maximum_replaceIndividual_eq_max i (v.1,v.2.1) hv x

theorem maximum_eq_max_competing_ae (B : CountableInstance) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : ℕ) :
    ∀ᵐ v ∂B.completeWorldLaw ν, B.maximum (v.1,v.2.1)=max (v.2.1 i) (B.competingMaximum i v) := by
  filter_upwards [B.maximum_replaceIndividual_eq_max_ae ν i] with v hv
  simpa only [Function.update_eq_self] using hv (v.2.1 i)

end ProphetSecretary.Limiting.CountableInstance
