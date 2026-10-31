import ProphetSecretary.Limiting.DirectApproximationSchedule
import ProphetSecretary.Limiting.DirectIndividualLikelihoodLaw
import ProphetSecretary.Model.StandbyIidReward

/-!
# The actual virtual marginal of the fixed direct schedule

The chosen count and cutoff belong to the unperturbed schedule. The virtual
law is the positive cutoff intensity divided by that count with the remaining
mass at zero. The retained-plus-iid representation is equality of the actual
finite marginals, including all zero observations.
-/

open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

noncomputable def directVirtualOfferLaw (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    ProbabilityMeasure ℝ :=
  rareProbabilityLaw (B.directTruncation m).intensity (B.directVirtualCount hZero m)
    (by exact_mod_cast B.directVirtualCount_positive hZero m) (B.directVirtualCount_rate_le hZero m)

lemma directVirtualOfferLaw_bounds (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    ∀ᵐ x ∂(B.directVirtualOfferLaw hZero m : Measure ℝ), x∈Icc (0 : ℝ) B.cap :=
  rareProbabilityLaw_bounds (B.directTruncation m).intensity B.cap
    ((B.directTruncation m).intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩))
    (B.directVirtualCount hZero m) (by exact_mod_cast B.directVirtualCount_positive hZero m)
    (B.directVirtualCount_rate_le hZero m)

noncomputable def directVirtualOfferInstance (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    Instance (B.directVirtualCount hZero m) :=
  iidOfferInstance (B.directVirtualOfferLaw hZero m : Measure ℝ)
    ((B.directVirtualOfferLaw_bounds hZero m).mono (fun _ hx => hx.1)) (B.directVirtualCount hZero m)

lemma directFiniteApproximation_eq_appendVirtual (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    B.directFiniteApproximation hZero m=(B.individualPrefix m).appendIndependent (B.directVirtualOfferInstance hZero m) := by
  unfold directFiniteApproximation
  rw [←(B.directTruncation m).rareDesign_eq_finitePoissonApproximation (B.directRefinementIndex hZero m)]
  apply Model.Instance.eq_of_law_eq
  rfl

end ProphetSecretary.Limiting.CountableInstance
