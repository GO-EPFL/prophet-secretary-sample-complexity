import ProphetSecretary.Limiting.Support
import ProphetSecretary.Limiting.ZeroIntensity
import ProphetSecretary.Probability.IndependentNullSections

/-!
# Coincident anonymous marks belong to the intensity's atoms

Conditional on the actual count, two different points have independent
normalized mark laws. Null singleton sections exclude collisions outside
any measurable set containing the intensity atoms. Zero intensity has the
literal empty-configuration law.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting

private lemma independent_equal_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {μ : Measure ℝ} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hI : IndepFun X Y P) (hX : Measurable X) (hY : Measurable Y) (hLaw : HasLaw X μ P)
    {A : Set ℝ} (hA : MeasurableSet A) (hNull : ∀ y∉A, μ {y}=0) :
    ∀ᵐ ω ∂P, X ω=Y ω → X ω∈A := by
  apply ProphetSecretary.Probability.indepFun_ae_of_sections hI hX hY hLaw (p := fun x y => x=y → x∈A)
  · have hSet : {p : ℝ × ℝ | p.1=p.2 → p.1∈A}=
        {p : ℝ × ℝ | p.1≠p.2}∪Prod.fst ⁻¹' A := by ext p; simp only [mem_setOf_eq,mem_union,mem_preimage,imp_iff_not_or]
    rw [hSet]
    exact (measurableSet_eq_fun measurable_fst measurable_snd).compl.union (hA.preimage measurable_fst)
  · intro y
    by_cases hy : y∈A
    · exact Eventually.of_forall (fun x hx => hx.symm ▸ hy)
    · have hAvoid : ∀ᵐ x ∂μ, x≠y := by
        simpa only [mem_singleton_iff] using measure_eq_zero_iff_ae_notMem.mp (hNull y hy)
      exact hAvoid.mono (fun _ hn he => (hn he).elim)

lemma measurableSet_configuration_equal_marks_mem {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet {ω : Configuration | ∀ j k : Fin ω.1, j≠k → (ω.2 j).2=(ω.2 k).2 → (ω.2 j).2∈A} := by
  apply measurableSet_setOf.mpr
  apply measurable_of_configuration_branches
  intro N
  apply measurableSet_setOf.mp
  change MeasurableSet {v : Fin N → Point | ∀ j k, j≠k → (v j).2=(v k).2 → (v j).2∈A}
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro _hjk
  have hSet : {v : Fin N → Point | (v j).2=(v k).2 → (v j).2∈A}=
      {v | (v j).2≠(v k).2}∪(fun v => (v j).2) ⁻¹' A := by
    ext v
    simp only [mem_setOf_eq,mem_union,mem_preimage,imp_iff_not_or]
  rw [hSet]
  exact (measurableSet_eq_fun (measurable_pi_apply j).snd (measurable_pi_apply k).snd).compl.union
    (hA.preimage (measurable_pi_apply j).snd)

lemma configuration_equal_marks_mem (μ : FiniteMeasure ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    (hNull : ∀ y∉A, (μ : Measure ℝ) {y}=0) :
    ∀ᵐ ω ∂configurationLaw μ, ∀ j k : Fin ω.1,
      j≠k → (ω.2 j).2=(ω.2 k).2 → (ω.2 j).2∈A := by
  by_cases hμ : μ=0
  · subst μ
    rw [configurationLaw_zero,ae_dirac_iff (measurableSet_configuration_equal_marks_mem hA)]
    intro j
    exact Fin.elim0 j
  · apply ae_configuration_of_fibers μ _ (measurableSet_configuration_equal_marks_mem hA)
    intro N
    have hPair (j k : Fin N) : ∀ᵐ v ∂arrayLaw μ N,
        j≠k → (v j).2=(v k).2 → (v j).2∈A := by
      by_cases hjk : j=k
      · exact Eventually.of_forall (fun _ hn => (hn hjk).elim)
      · have hI := ((array_points_independent μ N).indepFun hjk).comp measurable_snd measurable_snd
        have hMP : MeasurePreserving (fun v : Fin N → Point => (v j).2)
            (arrayLaw μ N) (μ.normalize : Measure ℝ) :=
          (measurePreserving_snd : MeasurePreserving (Prod.snd : Point → ℝ) (pointLaw μ) (μ.normalize : Measure ℝ)).comp
            (measurePreserving_eval (fun _ : Fin N => pointLaw μ) j)
        have hNull' (y : ℝ) (hy : y∉A) : (μ.normalize : Measure ℝ) {y}=0 := by
          rw [μ.toMeasure_normalize_eq_of_nonzero hμ,Measure.smul_apply,hNull y hy,smul_zero]
        have h := independent_equal_mem hI (measurable_pi_apply j).snd (measurable_pi_apply k).snd hMP.hasLaw hA hNull'
        exact h.mono (fun _ hv _ => hv)
    exact ae_all_iff.mpr (fun j => ae_all_iff.mpr (hPair j))

end ProphetSecretary.Limiting
