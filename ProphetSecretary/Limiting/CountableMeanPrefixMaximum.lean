import ProphetSecretary.Limiting.CountableMeanContractionPrefix
import ProphetSecretary.Model.ProphetWinner

/-!
# The deterministic maximum of a finite prefix of marginal means

This quantity is the prophet benchmark of the mean-contracted finite
prefix, rather than the expected maximum of the original random prefix.
Each marginal mean is at most the original full prophet expectation.
A nonempty finite prefix has a maximizing identity, including when every
mean is zero.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma expectedMaximum_nonnegative (B : CountableInstance) : 0≤B.expectedMaximum :=
  integral_nonneg_of_ae (B.maximum_bounded.mono (fun _ hx => B.terminal.property.trans hx.1))

theorem individualMean_le_expectedMaximum (B : CountableInstance) (i : ℕ) :
    B.individualMean i≤B.expectedMaximum := by
  have hMP : MeasurePreserving (fun v : ValueWorld => v.2 i) B.valueLaw (B.individuals i : Measure ℝ) :=
    (B.individualValue_measurePreserving i).comp measurePreserving_snd
  have hMean := hMP.hasLaw.integral_comp (measurable_id : Measurable (fun x : ℝ => x)).aestronglyMeasurable
  have hInt := hMP.integrable_comp_of_integrable (B.integrable_individualValue i)
  calc
    _ = ∫ v : ValueWorld, v.2 i ∂B.valueLaw := hMean.symm
    _ ≤ ∫ v : ValueWorld, B.maximum v ∂B.valueLaw :=
      integral_mono_ae hInt B.integrable_maximum (B.individual_le_maximum.mono (fun _ hv => hv i))

noncomputable def meanPrefixMaximum (B : CountableInstance) (N : ℕ) : ℝ :=
  Model.Instance.maximum (fun i : Fin N => B.individualMean i.val)

lemma meanPrefixMaximum_nonnegative (B : CountableInstance) (N : ℕ) :
    0≤B.meanPrefixMaximum N := Model.Instance.maximum_nonnegative _

lemma meanPrefixMaximum_le_expectedMaximum (B : CountableInstance) (N : ℕ) :
    B.meanPrefixMaximum N≤B.expectedMaximum :=
  Model.Instance.maximum_le _ B.expectedMaximum_nonnegative (fun i => B.individualMean_le_expectedMaximum i.val)

lemma meanPrefixMaximum_le_cap (B : CountableInstance) (N : ℕ) :
    B.meanPrefixMaximum N≤(B.cap : ℝ) :=
  Model.Instance.maximum_le _ B.cap.property (fun i => (B.individualMean_mem_cap i.val).2)

theorem exists_meanPrefix_maximizer (B : CountableInstance) {N : ℕ} (hN : 0<N) :
    ∃ i : Fin N, B.individualMean i.val=B.meanPrefixMaximum N := by
  by_cases hPositive : 0<B.meanPrefixMaximum N
  · obtain ⟨i,hi⟩ := Model.exists_prophetWins (x := fun i : Fin N => B.individualMean i.val) hPositive
    exact ⟨i,hi.2.1⟩
  · have hZero : B.meanPrefixMaximum N=0 := le_antisymm (not_lt.mp hPositive) (B.meanPrefixMaximum_nonnegative N)
    let i : Fin N := ⟨0,hN⟩
    refine ⟨i,le_antisymm (Model.Instance.le_maximum (fun j : Fin N => B.individualMean j.val) i) ?_⟩
    rw [hZero]
    exact (B.individualMean_mem_cap i.val).1

end ProphetSecretary.Limiting.CountableInstance
