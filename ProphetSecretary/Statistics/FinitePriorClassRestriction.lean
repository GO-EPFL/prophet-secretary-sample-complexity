import ProphetSecretary.Statistics.FinitePriorClassifier
import ProphetSecretary.Statistics.FinitePriorPosteriorWeights

/-!
# Restricting the actual finite posterior to the selected valid class

The invalid-atom flag is observable once an atom is fixed. Pulling this flag out
of conditional expectation identifies the excluded posterior mass with the sum
of actual atom posterior weights. The normalized retained weights are constructed
from observed data, with the zero-retained-mass case kept explicit.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model ProphetSecretary.Analysis
variable {n : ℕ}

noncomputable def invalidAtomFlag (F : FinitePrior n) (N h : ℕ) (hh : h≤N)
    (Sstar : ℝ) (θ : Fin F.size) (ω : BaseWorld F N) : ℝ :=
  (invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment).indicator 1
    (F.classifierPrefix N h hh ω)

lemma invalidAtomFlag_stronglyMeasurable (F : FinitePrior n) (N h : ℕ) (hh : h≤N)
    (Sstar : ℝ) (θ : Fin F.size) :
    StronglyMeasurable[F.dataSigma N 0 h] (F.invalidAtomFlag N h hh Sstar θ) := by
  have hg : StronglyMeasurable ((invalidFirstMomentClass (n:=n) (h:=h) Sstar (F.offerInstance θ).totalFirstMoment).indicator (fun _ => (1:ℝ))) :=
    (measurable_const.indicator (measurableSet_invalidFirstMomentClass Sstar _)).stronglyMeasurable
  exact hg.comp_measurable (F.classifierPrefix_stronglyMeasurable N h hh).measurable

lemma invalidAtomFlag_mem_unit (F : FinitePrior n) (N h : ℕ) (hh : h≤N)
    (Sstar : ℝ) (θ : Fin F.size) (ω : BaseWorld F N) :
    F.invalidAtomFlag N h hh Sstar θ ω∈Icc (0:ℝ) 1 := by
  simp only [invalidAtomFlag,Set.indicator_apply,Pi.one_apply]
  split_ifs <;> norm_num

lemma invalidClassifierIndicator_eq_sum (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) :
    F.invalidClassifierIndicator N h hh Sstar=
      ∑ θ : Fin F.size, F.invalidAtomFlag N h hh Sstar θ*F.atomIndicator θ := by
  funext ω
  simp only [Finset.sum_apply,Pi.mul_apply,atomIndicator]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rfl

/-- This is an identity for the actual posterior, not a posterior-mass interface. -/
theorem posteriorExcludedMass_eq_sum (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) :
    F.posteriorExcludedMass N h hh Sstar =ᵐ[F.law N]
      (fun ω => ∑ θ : Fin F.size,
        F.invalidAtomFlag N h hh Sstar θ ω*F.atomPosterior N 0 h θ ω) := by
  have hProd (θ : Fin F.size) : Integrable (F.invalidAtomFlag N h hh Sstar θ*F.atomIndicator θ) (F.law N) := by
    have hB : ∀ᵐ ω ∂F.law N, ‖F.invalidAtomFlag N h hh Sstar θ ω‖≤1 := Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (F.invalidAtomFlag_mem_unit N h hh Sstar θ ω).1]
      exact (F.invalidAtomFlag_mem_unit N h hh Sstar θ ω).2
    exact (F.atomIndicator_integrable N θ).bdd_mul
      ((F.invalidAtomFlag_stronglyMeasurable N h hh Sstar θ).mono (F.dataSigma_le N 0 h)).aestronglyMeasurable hB
  have hLin := condExp_finsetSum (μ:=F.law N) (s:=Finset.univ) (fun θ _ => hProd θ) (F.dataSigma N 0 h)
  have hPull (θ : Fin F.size) := condExp_mul_of_stronglyMeasurable_left (μ:=F.law N)
    (F.invalidAtomFlag_stronglyMeasurable N h hh Sstar θ) (hProd θ) (F.atomIndicator_integrable N θ)
  unfold posteriorExcludedMass
  rw [F.invalidClassifierIndicator_eq_sum]
  apply hLin.trans
  have hAll := ae_all_iff.mpr hPull
  filter_upwards [hAll] with ω hω
  simp only [Finset.sum_apply,atomPosterior]
  exact Finset.sum_congr rfl fun θ _ => hω θ

end ProphetSecretary.Statistics.FinitePrior
