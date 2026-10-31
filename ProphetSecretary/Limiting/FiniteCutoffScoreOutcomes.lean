import ProphetSecretary.Limiting.CoarsePoissonObservable

/-!
# Actual finite coarse score-weighted reward and duration

Clamped coordinate tests equal the actual bounded reward and unit elapsed
duration. The score is a function of the complete virtual offer vector,
used only in the expectation, including offers arriving after stopping.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting
variable {n N : ℕ}

lemma appendIndependent_bounded (P : Model.Instance n) (Q : Model.Instance N) {H : ℝ}
    (hP : ∀ i, ∀ᵐ x ∂P.law i, x≤H) (hQ : ∀ i, ∀ᵐ x ∂Q.law i, x≤H) :
    ∀ i, ∀ᵐ x ∂(P.appendIndependent Q).law i, x≤H := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [Model.Instance.appendIndependent,Fin.addCases_left] using hP i
  | right i => simpa only [Model.Instance.appendIndependent,Fin.addCases_right] using hQ i

lemma RandomizedHybridPolicy.finiteCutoffEvaluation_score_coordinate_tests
    (π : RandomizedHybridPolicy n)
    (P : Model.Instance n) (Q : Model.Instance N) (d : ℝ) (H : ℝ≥0)
    (hP : ∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ)) (hQ : ∀ i, ∀ᵐ x ∂Q.law i, x≤(H:ℝ))
    (s : (Fin N → ℝ) → ℝ) (hs : Measurable s) (hsInt : Integrable s Q.valuesLaw) :
    let Γ := π.finiteCutoffEvaluation N d
    (Integrable (fun ω : Γ.World => s (fun j => ω.1 (j.natAdd n))*Γ.realizedReward ω)
        ((P.appendIndependent Q).worldLaw π.seedLaw) ∧
      (∫ ω : Γ.World, s (fun j => ω.1 (j.natAdd n))*Γ.realizedReward ω
        ∂(P.appendIndependent Q).worldLaw π.seedLaw)=
      ∫ ω : Model.World N (Model.World n π.Seed), s ω.1*boundedClamp H
        (π.rule.observableReward 0 (ProphetSecretary.Probability.finiteMeasureOrZero
          (thresholdedOfferCountingMeasure d (fun j => (ω.2.1 j,ω.1 j))),ω.2.2))
        ∂Q.worldLaw (P.worldLaw π.seedLaw)) ∧
    (Integrable (fun ω : Γ.World => s (fun j => ω.1 (j.natAdd n))*Γ.realizedDuration ω)
        ((P.appendIndependent Q).worldLaw π.seedLaw) ∧
      (∫ ω : Γ.World, s (fun j => ω.1 (j.natAdd n))*Γ.realizedDuration ω
        ∂(P.appendIndependent Q).worldLaw π.seedLaw)=
      ∫ ω : Model.World N (Model.World n π.Seed), s ω.1*boundedClamp 1
        (π.rule.observableDuration (ProphetSecretary.Probability.finiteMeasureOrZero
          (thresholdedOfferCountingMeasure d (fun j => (ω.2.1 j,ω.1 j))),ω.2.2))
        ∂Q.worldLaw (P.worldLaw π.seedLaw)) := by
  let Γ := π.finiteCutoffEvaluation N d
  let ΦR : (ℝ × ℝ) × Model.World n π.Seed → ℝ := fun z => boundedClamp H z.1.1
  let ΦT : (ℝ × ℝ) × Model.World n π.Seed → ℝ := fun z => boundedClamp 1 z.1.2
  have hRM : Measurable ΦR := (boundedClamp H).continuous.measurable.comp (by fun_prop)
  have hTM : Measurable ΦT := (boundedClamp 1).continuous.measurable.comp (by fun_prop)
  have hRB (z) : ‖ΦR z‖≤(H:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (boundedClamp_bounds H _).1]
    exact (boundedClamp_bounds H _).2
  have hTB (z) : ‖ΦT z‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (boundedClamp_bounds 1 _).1]
    exact (boundedClamp_bounds 1 _).2
  have hR := π.finiteCutoffEvaluation_scored_observables P Q d s hs hsInt ΦR hRM hRB
  have hT := π.finiteCutoffEvaluation_scored_observables P Q d s hs hsInt ΦT hTM hTB
  have hRanges := finite_policy_outcome_ranges Γ (P.appendIndependent Q) H (appendIndependent_bounded P Q hP hQ)
  have hRTarget : (fun ω : Γ.World => s (fun j => ω.1 (j.natAdd n))*ΦR
      ((Γ.realizedReward ω,Γ.realizedDuration ω),Model.Instance.projectWorld (Fin.castAddEmb N) ω)) =ᵐ[(P.appendIndependent Q).worldLaw π.seedLaw]
      (fun ω => s (fun j => ω.1 (j.natAdd n))*Γ.realizedReward ω) := by
    filter_upwards [hRanges] with ω hω
    exact congrArg (fun x => s (fun j => ω.1 (j.natAdd n))*x) (boundedClamp_eq H hω.1)
  have hTTarget : (fun ω : Γ.World => s (fun j => ω.1 (j.natAdd n))*ΦT
      ((Γ.realizedReward ω,Γ.realizedDuration ω),Model.Instance.projectWorld (Fin.castAddEmb N) ω)) =ᵐ[(P.appendIndependent Q).worldLaw π.seedLaw]
      (fun ω => s (fun j => ω.1 (j.natAdd n))*Γ.realizedDuration ω) := by
    filter_upwards [hRanges] with ω hω
    exact congrArg (fun x => s (fun j => ω.1 (j.natAdd n))*x) (boundedClamp_eq 1 hω.2)
  exact ⟨⟨hR.1.congr hRTarget,(integral_congr_ae hRTarget).symm.trans hR.2.2⟩,
    ⟨hT.1.congr hTTarget,(integral_congr_ae hTTarget).symm.trans hT.2.2⟩⟩
end ProphetSecretary.Limiting
