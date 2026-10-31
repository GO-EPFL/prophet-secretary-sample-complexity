import ProphetSecretary.Statistics.FinitePriorHypothetical
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Actual finite posterior weights from observed training data

Each weight is a conditional expectation of a hidden-atom indicator. The simplex
identity and observable representatives follow from conditional expectation,
rather than being hypotheses on an abstract posterior interface.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
variable {n : ℕ}

def atomIndicator (F : FinitePrior n) {N : ℕ} (θ : Fin F.size) (ω : BaseWorld F N) : ℝ :=
  if ω.1=θ then 1 else 0

lemma measurable_atomIndicator (F : FinitePrior n) (N : ℕ) (θ : Fin F.size) :
    Measurable (F.atomIndicator (N:=N) θ) :=
  (measurable_of_finite (fun t : Fin F.size => if t=θ then (1:ℝ) else 0)).comp measurable_fst

lemma atomIndicator_mem_unit (F : FinitePrior n) {N : ℕ} (θ : Fin F.size) (ω : BaseWorld F N) :
    F.atomIndicator θ ω∈Icc (0:ℝ) 1 := by
  unfold atomIndicator
  split_ifs <;> norm_num

lemma atomIndicator_integrable (F : FinitePrior n) (N : ℕ) (θ : Fin F.size) :
    Integrable (F.atomIndicator (N:=N) θ) (F.law N) :=
  Integrable.of_bound (F.measurable_atomIndicator N θ).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (F.atomIndicator_mem_unit θ ω).1]
      exact (F.atomIndicator_mem_unit θ ω).2)

lemma sum_atomIndicator (F : FinitePrior n) {N : ℕ} (ω : BaseWorld F N) :
    (∑ θ : Fin F.size, F.atomIndicator θ ω)=1 := by simp [atomIndicator]

noncomputable def atomPosterior (F : FinitePrior n) (N b k : ℕ) (θ : Fin F.size) : BaseWorld F N → ℝ :=
  (F.law N)[F.atomIndicator θ|F.dataSigma N b k]

lemma atomPosterior_stronglyMeasurable (F : FinitePrior n) (N b k : ℕ) (θ : Fin F.size) :
    StronglyMeasurable[F.dataSigma N b k] (F.atomPosterior N b k θ) := stronglyMeasurable_condExp

lemma atomPosterior_mem_unit (F : FinitePrior n) (N b k : ℕ) (θ : Fin F.size) :
    ∀ᵐ ω ∂F.law N, F.atomPosterior N b k θ ω∈Icc (0:ℝ) 1 :=
  ProphetSecretary.Probability.conditionalPosterior_mem_unit (ℱ:=F.dataFiltration N b)
    (F.measurable_atomIndicator N θ) (Eventually.of_forall (F.atomIndicator_mem_unit θ)) k

lemma sum_atomPosterior (F : FinitePrior n) (N b k : ℕ) :
    ∀ᵐ ω ∂F.law N, (∑ θ : Fin F.size, F.atomPosterior N b k θ ω)=1 := by
  have hSum : (∑ θ : Fin F.size, F.atomIndicator (N:=N) θ)=(fun _ => (1:ℝ)) := by
    funext ω
    simpa only [Finset.sum_apply] using F.sum_atomIndicator ω
  have h := condExp_finsetSum (μ:=F.law N) (s:=Finset.univ)
    (fun θ _ => F.atomIndicator_integrable N θ) (F.dataSigma N b k)
  rw [hSum,condExp_const (F.dataSigma_le N b k)] at h
  filter_upwards [h] with ω hω
  simpa only [Finset.sum_apply,atomPosterior] using hω.symm

noncomputable def atomPosteriorFromObservation (F : FinitePrior n) (N b k : ℕ) (θ : Fin F.size) : ValueArray n N → ℝ :=
  Classical.choose ((F.atomPosterior_stronglyMeasurable N b k θ).exists_eq_measurable_comp)

lemma stronglyMeasurable_atomPosteriorFromObservation (F : FinitePrior n) (N b k : ℕ) (θ : Fin F.size) :
    StronglyMeasurable (F.atomPosteriorFromObservation N b k θ) :=
  (Classical.choose_spec ((F.atomPosterior_stronglyMeasurable N b k θ).exists_eq_measurable_comp)).1

lemma atomPosterior_eq_observed (F : FinitePrior n) (N b k : ℕ) (θ : Fin F.size) (ω : BaseWorld F N) :
    F.atomPosterior N b k θ ω=F.atomPosteriorFromObservation N b k θ (F.observe N b k ω) :=
  congrFun (Classical.choose_spec ((F.atomPosterior_stronglyMeasurable N b k θ).exists_eq_measurable_comp)).2 ω

lemma prior_weight_sum_real (F : FinitePrior n) : (∑ θ : Fin F.size, (F.weight θ:ℝ))=1 := by
  exact_mod_cast F.weight_sum

lemma prior_weight_mem_unit (F : FinitePrior n) (θ : Fin F.size) : (F.weight θ:ℝ)∈Icc (0:ℝ) 1 := by
  refine ⟨(F.weight θ).coe_nonneg,?_⟩
  have h := Finset.single_le_sum (fun t (_ : t∈(Finset.univ : Finset (Fin F.size))) => (F.weight t).coe_nonneg)
    (Finset.mem_univ θ)
  rw [F.prior_weight_sum_real] at h
  exact h

noncomputable def nonnegativePosteriorWeight (F : FinitePrior n) (N b k : ℕ) (d : ValueArray n N) (θ : Fin F.size) : ℝ :=
  max 0 (F.atomPosteriorFromObservation N b k θ d)

noncomputable def posteriorWeightTotal (F : FinitePrior n) (N b k : ℕ) (d : ValueArray n N) : ℝ :=
  ∑ θ : Fin F.size, F.nonnegativePosteriorWeight N b k d θ

/-- Totalization on impossible observations uses the given prior. -/
noncomputable def observablePosteriorWeight (F : FinitePrior n) (N b k : ℕ) (d : ValueArray n N) (θ : Fin F.size) : ℝ :=
  if 0<F.posteriorWeightTotal N b k d then
    F.nonnegativePosteriorWeight N b k d θ/F.posteriorWeightTotal N b k d else F.weight θ

lemma measurable_observablePosteriorWeight (F : FinitePrior n) (N b k : ℕ) (θ : Fin F.size) :
    Measurable (fun d => F.observablePosteriorWeight N b k d θ) := by
  have hρ (t : Fin F.size) : Measurable (fun d => F.nonnegativePosteriorWeight N b k d t) :=
    measurable_const.max (F.stronglyMeasurable_atomPosteriorFromObservation N b k t).measurable
  have hT : Measurable (F.posteriorWeightTotal N b k) := Finset.measurable_sum Finset.univ (fun t _ => hρ t)
  exact ((hρ θ).div hT).ite (measurableSet_lt measurable_const hT) measurable_const

lemma sum_observablePosteriorWeight (F : FinitePrior n) (N b k : ℕ) (d : ValueArray n N) :
    (∑ θ : Fin F.size, F.observablePosteriorWeight N b k d θ)=1 := by
  by_cases hT : 0<F.posteriorWeightTotal N b k d
  · simp only [observablePosteriorWeight,if_pos hT]
    rw [←Finset.sum_div]
    exact div_self (ne_of_gt hT)
  · simp only [observablePosteriorWeight,if_neg hT]
    exact F.prior_weight_sum_real

lemma observablePosteriorWeight_mem_unit (F : FinitePrior n) (N b k : ℕ) (d : ValueArray n N) (θ : Fin F.size) :
    F.observablePosteriorWeight N b k d θ∈Icc (0:ℝ) 1 := by
  by_cases hT : 0<F.posteriorWeightTotal N b k d
  · rw [observablePosteriorWeight,if_pos hT]
    refine ⟨div_nonneg (le_max_left _ _) hT.le,(div_le_one hT).mpr ?_⟩
    exact Finset.single_le_sum (fun t _ => le_max_left 0 (F.atomPosteriorFromObservation N b k t d)) (Finset.mem_univ θ)
  · rw [observablePosteriorWeight,if_neg hT]
    exact F.prior_weight_mem_unit θ

/-- The all-outcome simplex totalization agrees with the actual CE posterior on
its observed-data law. It supplies no unobserved data to a policy. -/
theorem observablePosteriorWeight_eq_ae (F : FinitePrior n) (N b k : ℕ) :
    ∀ᵐ ω ∂F.law N, ∀ θ : Fin F.size,
      F.observablePosteriorWeight N b k (F.observe N b k ω) θ=F.atomPosterior N b k θ ω := by
  have hAll : ∀ᵐ ω ∂F.law N, ∀ θ : Fin F.size, F.atomPosterior N b k θ ω∈Icc (0:ℝ) 1 :=
    ae_all_iff.mpr (F.atomPosterior_mem_unit N b k)
  filter_upwards [hAll,F.sum_atomPosterior N b k] with ω hU hSum
  have hρ (θ : Fin F.size) : F.nonnegativePosteriorWeight N b k (F.observe N b k ω) θ=F.atomPosterior N b k θ ω := by
    rw [nonnegativePosteriorWeight,←F.atomPosterior_eq_observed N b k θ ω,max_eq_right (hU θ).1]
  have hT : F.posteriorWeightTotal N b k (F.observe N b k ω)=1 := by
    simp only [posteriorWeightTotal,hρ]
    exact hSum
  intro θ
  rw [observablePosteriorWeight,hT,if_pos zero_lt_one,hρ,div_one]

end ProphetSecretary.Statistics.FinitePrior
