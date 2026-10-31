import ProphetSecretary.Statistics.FinitePriorClassRestriction

/-!
# Observable normalization on the selected valid class

The prior atom list is fixed in a Bayes response. Its candidate first moments
can therefore be used to determine which atoms belong to the sample-selected
class, without observing nature's hidden atom. Retained mass zero is explicit;
normalization is a probability vector only on positive retained mass.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

def validClassObservation (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (d : ValueArray n N) (θ : Fin F.size) : Prop :=
  classifierPrefixRead n N h hh d∉invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment

lemma measurableSet_validClassObservation (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) (θ : Fin F.size) :
    MeasurableSet {d | F.validClassObservation N h hh Sstar d θ} :=
  ((measurableSet_invalidFirstMomentClass Sstar _).preimage (measurable_classifierPrefixRead n N h hh)).compl

noncomputable def retainedPosteriorWeight (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (d : ValueArray n N) (θ : Fin F.size) : ℝ :=
  if F.validClassObservation N h hh Sstar d θ then F.observablePosteriorWeight N 0 h d θ else 0

noncomputable def retainedPosteriorMass (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) (d : ValueArray n N) : ℝ :=
  ∑ θ : Fin F.size, F.retainedPosteriorWeight N h hh Sstar d θ

lemma retainedPosteriorWeight_nonneg (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (d : ValueArray n N) (θ : Fin F.size) : 0≤F.retainedPosteriorWeight N h hh Sstar d θ := by
  unfold retainedPosteriorWeight
  split_ifs
  · exact (F.observablePosteriorWeight_mem_unit N 0 h d θ).1
  · exact le_rfl

lemma measurable_retainedPosteriorWeight (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) (θ : Fin F.size) :
    Measurable (fun d => F.retainedPosteriorWeight N h hh Sstar d θ) :=
  (F.measurable_observablePosteriorWeight N 0 h θ).ite (F.measurableSet_validClassObservation N h hh Sstar θ) measurable_const

lemma measurable_retainedPosteriorMass (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) :
    Measurable (F.retainedPosteriorMass N h hh Sstar) :=
  Finset.measurable_sum Finset.univ (fun θ _ => F.measurable_retainedPosteriorWeight N h hh Sstar θ)

lemma retainedPosteriorMass_mem_unit (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) (d : ValueArray n N) :
    F.retainedPosteriorMass N h hh Sstar d∈Icc (0:ℝ) 1 := by
  refine ⟨Finset.sum_nonneg (fun θ _ => F.retainedPosteriorWeight_nonneg N h hh Sstar d θ),?_⟩
  calc
    F.retainedPosteriorMass N h hh Sstar d≤∑ θ : Fin F.size, F.observablePosteriorWeight N 0 h d θ := by
      apply Finset.sum_le_sum
      intro θ _
      unfold retainedPosteriorWeight
      split_ifs
      · exact le_rfl
      · exact (F.observablePosteriorWeight_mem_unit N 0 h d θ).1
    _=1 := F.sum_observablePosteriorWeight N 0 h d

noncomputable def validPosteriorWeight (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (d : ValueArray n N) (θ : Fin F.size) : ℝ :=
  if 0<F.retainedPosteriorMass N h hh Sstar d then
    F.retainedPosteriorWeight N h hh Sstar d θ/F.retainedPosteriorMass N h hh Sstar d else 0

lemma measurable_validPosteriorWeight (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) (θ : Fin F.size) :
    Measurable (fun d => F.validPosteriorWeight N h hh Sstar d θ) :=
  ((F.measurable_retainedPosteriorWeight N h hh Sstar θ).div (F.measurable_retainedPosteriorMass N h hh Sstar)).ite
    (measurableSet_lt measurable_const (F.measurable_retainedPosteriorMass N h hh Sstar)) measurable_const

lemma validPosteriorWeight_nonneg (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (d : ValueArray n N) (θ : Fin F.size) : 0≤F.validPosteriorWeight N h hh Sstar d θ := by
  unfold validPosteriorWeight
  split_ifs with hpos
  · exact div_nonneg (F.retainedPosteriorWeight_nonneg N h hh Sstar d θ) hpos.le
  · exact le_rfl

lemma sum_validPosteriorWeight (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (d : ValueArray n N) (hpos : 0<F.retainedPosteriorMass N h hh Sstar d) :
    (∑ θ : Fin F.size, F.validPosteriorWeight N h hh Sstar d θ)=1 := by
  simp only [validPosteriorWeight,if_pos hpos]
  rw [←Finset.sum_div]
  exact div_self (ne_of_gt hpos)

lemma validPosteriorWeight_zero_on_invalid (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (d : ValueArray n N) (θ : Fin F.size) (hθ : ¬F.validClassObservation N h hh Sstar d θ) :
    F.validPosteriorWeight N h hh Sstar d θ=0 := by
  unfold validPosteriorWeight retainedPosteriorWeight
  split_ifs <;> simp only [zero_div]

noncomputable def validPosteriorPrior (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (d : ValueArray n N) (hpos : 0<F.retainedPosteriorMass N h hh Sstar d) : FinitePrior n where
  size := F.size
  weight θ := ⟨F.validPosteriorWeight N h hh Sstar d θ,F.validPosteriorWeight_nonneg N h hh Sstar d θ⟩
  weight_sum := by
    have hSum := F.sum_validPosteriorWeight N h hh Sstar d hpos
    apply NNReal.coe_injective
    rw [NNReal.coe_sum,NNReal.coe_one]
    change (∑ θ : Fin F.size, F.validPosteriorWeight N h hh Sstar d θ)=1
    exact hSum
  offerInstance := F.offerInstance
  target := F.target

lemma retained_weight_add_invalid_weight (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (θ : Fin F.size) (ω : BaseWorld F N) :
    F.retainedPosteriorWeight N h hh Sstar (F.observe N 0 h ω) θ+
      F.invalidAtomFlag N h hh Sstar θ ω*F.observablePosteriorWeight N 0 h (F.observe N 0 h ω) θ=
      F.observablePosteriorWeight N 0 h (F.observe N 0 h ω) θ := by
  unfold retainedPosteriorWeight validClassObservation invalidAtomFlag
  rw [←F.classifierPrefix_eq_observed N h hh ω]
  by_cases hInv : F.classifierPrefix N h hh ω∈invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment
  · simp only [hInv,not_true_eq_false,if_false,Set.indicator_of_mem hInv,Pi.one_apply,one_mul,zero_add]
  · simp only [hInv,not_false_eq_true,if_true,Set.indicator_of_notMem hInv,zero_mul,add_zero]

/-- The retained observable mass equals one minus the actual excluded posterior
mass on the experiment, so both notions of class restriction coincide. -/
theorem retainedPosteriorMass_add_excluded_eq_one (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) :
    ∀ᵐ ω ∂F.law N,
      F.retainedPosteriorMass N h hh Sstar (F.observe N 0 h ω)+F.posteriorExcludedMass N h hh Sstar ω=1 := by
  filter_upwards [F.posteriorExcludedMass_eq_sum N h hh Sstar,F.observablePosteriorWeight_eq_ae N 0 h] with ω hξ hρ
  rw [hξ]
  have hSum := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl
    (fun θ (_ : θ∈(Finset.univ : Finset (Fin F.size))) => F.retained_weight_add_invalid_weight N h hh Sstar θ ω)
  rw [Finset.sum_add_distrib,F.sum_observablePosteriorWeight N 0 h (F.observe N 0 h ω)] at hSum
  change F.retainedPosteriorMass N h hh Sstar (F.observe N 0 h ω)+_=1 at hSum
  convert hSum using 1
  congr 1
  exact Finset.sum_congr rfl fun θ _ => congrArg (F.invalidAtomFlag N h hh Sstar θ ω*·) (hρ θ).symm

lemma validClassObservation_iff (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (d : ValueArray n N) (θ : Fin F.size) :
    F.validClassObservation N h hh Sstar d θ ↔
      (if selectLowFirstMoment Sstar (classifierPrefixRead n N h hh d) then
        (F.offerInstance θ).totalFirstMoment≤3*Sstar else Sstar≤(F.offerInstance θ).totalFirstMoment) := by
  cases hClass : selectLowFirstMoment Sstar (classifierPrefixRead n N h hh d) <;>
    simp only [validClassObservation,invalidFirstMomentClass,Set.mem_setOf_eq,hClass,Bool.false_eq_true,Bool.true_eq_false,
      false_and,true_and,false_or,or_false,not_lt,if_false,if_true]

/-- Every positive-weight atom of the normalized posterior belongs to the selected
valid class. Atoms with zero weight need no artificial class assumption. -/
lemma validPosteriorPrior_supported (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (d : ValueArray n N) (hpos : 0<F.retainedPosteriorMass N h hh Sstar d) (θ : Fin F.size)
    (hWeight : 0<(F.validPosteriorPrior N h hh Sstar d hpos).weight θ) :
    F.validClassObservation N h hh Sstar d θ := by
  by_contra hInvalid
  have hZero := F.validPosteriorWeight_zero_on_invalid N h hh Sstar d θ hInvalid
  have hReal : 0<F.validPosteriorWeight N h hh Sstar d θ := by exact_mod_cast hWeight
  linarith only [hReal,hZero]

end ProphetSecretary.Statistics.FinitePrior
