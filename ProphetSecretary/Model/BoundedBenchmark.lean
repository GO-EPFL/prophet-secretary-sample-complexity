import ProphetSecretary.Model.Truncation
import ProphetSecretary.Model.CompetitiveBasic

/-!
# Bounded instances suffice for the global competitive infimum

Both the benchmark and the full-information optimal reward ratio converge under capping.
The value convergence here uses the reconstructed policies from `Truncation`; it is not
inferred from convergence of values of random offers alone. Each limit keeps `n` fixed.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace ProphetSecretary.Model

lemma cap_competitiveRatio_tendsto {n : ℕ} (P : Instance n) (hP : P.HasPositiveFiniteMaximum) :
    Tendsto (fun H : ℝ≥0 => optimalScalarValue (P.cap H) 1 0 / (P.cap H).expectedMaximum)
      atTop (𝓝 (optimalScalarValue P 1 0 / P.expectedMaximum)) :=
  (optimalScalarValue_cap_tendsto P hP.1 zero_le_one le_rfl).div
    (P.cap_expectedMaximum_tendsto hP.1) hP.2.ne'

/-- Only positive finite benchmarks enter this infimum; zero-mean capped auxiliaries
remain allowed elsewhere in the development. -/
def boundedCompetitiveRatios : Set ℝ :=
  {r | ∃ (n : ℕ) (P : Instance n) (H : ℝ≥0), P.HasPositiveFiniteMaximum ∧
    (∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) ∧ r = optimalScalarValue P 1 0 / P.expectedMaximum}

noncomputable def boundedCompetitiveRatio : ℝ := sInf boundedCompetitiveRatios

lemma boundedCompetitiveRatios_nonempty : boundedCompetitiveRatios.Nonempty := by
  refine ⟨_, 1, unitOfferInstance, 1, unitOfferInstance_positiveFinite, ?_, rfl⟩
  intro i
  simp [unitOfferInstance]

lemma boundedCompetitiveRatios_bddBelow : BddBelow boundedCompetitiveRatios := by
  refine ⟨0, ?_⟩
  rintro r ⟨n, P, H, hP, _, rfl⟩
  exact (instanceCompetitiveRatio_mem_unitInterval P hP).1

lemma optimalCompetitiveRatio_le_boundedCompetitiveRatio :
    optimalCompetitiveRatio ≤ boundedCompetitiveRatio := by
  apply le_csInf boundedCompetitiveRatios_nonempty
  rintro r ⟨n, P, H, hP, _, rfl⟩
  exact optimalCompetitiveRatio_le_instance P hP

lemma boundedCompetitiveRatio_le_instance {n : ℕ} (P : Instance n) (hP : P.HasPositiveFiniteMaximum) :
    boundedCompetitiveRatio ≤ optimalScalarValue P 1 0 / P.expectedMaximum := by
  have hpos : ∀ᶠ H : ℝ≥0 in atTop, 0 < (P.cap H).expectedMaximum :=
    (P.cap_expectedMaximum_tendsto hP.1).eventually (Ioi_mem_nhds hP.2)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (cap_competitiveRatio_tendsto P hP)
  filter_upwards [hpos] with H hH
  exact csInf_le boundedCompetitiveRatios_bddBelow
    ⟨n, P.cap H, H, ⟨P.cap_integrable_maximum H hP.1, hH⟩, P.cap_bounded H, rfl⟩

/-- The global prophet-secretary constant is unchanged if its infimum is restricted to
bounded finite independent instances. No common cap or common instance size is imposed. -/
theorem boundedCompetitiveRatio_eq_optimalCompetitiveRatio :
    boundedCompetitiveRatio = optimalCompetitiveRatio := by
  apply le_antisymm
  · apply le_csInf competitiveRatios_nonempty
    rintro r ⟨n, P, hP, rfl⟩
    exact boundedCompetitiveRatio_le_instance P hP
  · exact optimalCompetitiveRatio_le_boundedCompetitiveRatio

end ProphetSecretary.Model
