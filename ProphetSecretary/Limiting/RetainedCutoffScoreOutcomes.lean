import ProphetSecretary.Limiting.FiniteCutoffScoreOutcomes

/-!
# Retained-data scores in an actual finite coarse execution

Clamped coordinate tests equal the actual bounded reward and unit elapsed
duration. The score is a function of the complete retained observations,
used only in the expectation, including offers arriving after stopping.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting
variable {n N : ℕ}

lemma RandomizedHybridPolicy.finiteCutoffEvaluation_retained_score_coordinate_tests
    (π : RandomizedHybridPolicy n)
    (P : Model.Instance n) (Q : Model.Instance N) (d : ℝ) (H : ℝ≥0)
    (hP : ∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ)) (hQ : ∀ i, ∀ᵐ x ∂Q.law i, x≤(H:ℝ))
    (g : Model.World n π.Seed → ℝ) (hg : Measurable g) (hgb : ∀ v, ‖g v‖≤1) :
    let Γ := π.finiteCutoffEvaluation N d
    (Integrable (fun ω : Γ.World => g (Model.Instance.projectWorld (Fin.castAddEmb N) ω)*Γ.realizedReward ω)
        ((P.appendIndependent Q).worldLaw π.seedLaw) ∧
      (∫ ω : Γ.World, g (Model.Instance.projectWorld (Fin.castAddEmb N) ω)*Γ.realizedReward ω
        ∂(P.appendIndependent Q).worldLaw π.seedLaw)=
      ∫ ω : Model.World N (Model.World n π.Seed), g ω.2.2*boundedClamp H
        (π.rule.observableReward 0 (ProphetSecretary.Probability.finiteMeasureOrZero
          (thresholdedOfferCountingMeasure d (fun j => (ω.2.1 j,ω.1 j))),ω.2.2))
        ∂Q.worldLaw (P.worldLaw π.seedLaw)) ∧
    (Integrable (fun ω : Γ.World => g (Model.Instance.projectWorld (Fin.castAddEmb N) ω)*Γ.realizedDuration ω)
        ((P.appendIndependent Q).worldLaw π.seedLaw) ∧
      (∫ ω : Γ.World, g (Model.Instance.projectWorld (Fin.castAddEmb N) ω)*Γ.realizedDuration ω
        ∂(P.appendIndependent Q).worldLaw π.seedLaw)=
      ∫ ω : Model.World N (Model.World n π.Seed), g ω.2.2*boundedClamp 1
        (π.rule.observableDuration (ProphetSecretary.Probability.finiteMeasureOrZero
          (thresholdedOfferCountingMeasure d (fun j => (ω.2.1 j,ω.1 j))),ω.2.2))
        ∂Q.worldLaw (P.worldLaw π.seedLaw)) := by
  let Γ := π.finiteCutoffEvaluation N d
  let ΦR : (ℝ × ℝ) × Model.World n π.Seed → ℝ := fun z => g z.2*boundedClamp H z.1.1
  let ΦT : (ℝ × ℝ) × Model.World n π.Seed → ℝ := fun z => g z.2*boundedClamp 1 z.1.2
  have hRM : Measurable ΦR := (hg.comp measurable_snd).mul ((boundedClamp H).continuous.measurable.comp (by fun_prop))
  have hTM : Measurable ΦT := (hg.comp measurable_snd).mul ((boundedClamp 1).continuous.measurable.comp (by fun_prop))
  have hRB (z) : ‖ΦR z‖≤(H:ℝ) := by
    change ‖g z.2*boundedClamp H z.1.1‖≤(H:ℝ)
    rw [norm_mul]
    have hb : ‖boundedClamp H z.1.1‖≤(H:ℝ) := by
      rw [Real.norm_eq_abs,abs_of_nonneg (boundedClamp_bounds H _).1]
      exact (boundedClamp_bounds H _).2
    exact (mul_le_mul (hgb z.2) hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hTB (z) : ‖ΦT z‖≤1 := by
    change ‖g z.2*boundedClamp 1 z.1.2‖≤1
    rw [norm_mul]
    have hb : ‖boundedClamp 1 z.1.2‖≤1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (boundedClamp_bounds 1 _).1]
      exact (boundedClamp_bounds 1 _).2
    exact (mul_le_mul (hgb z.2) hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hR := π.finiteCutoffEvaluation_scored_observables P Q d (fun _ => (1:ℝ)) measurable_const
    (integrable_const 1) ΦR hRM hRB
  have hT := π.finiteCutoffEvaluation_scored_observables P Q d (fun _ => (1:ℝ)) measurable_const
    (integrable_const 1) ΦT hTM hTB
  have hRanges := finite_policy_outcome_ranges Γ (P.appendIndependent Q) H (appendIndependent_bounded P Q hP hQ)
  have hRTarget : (fun ω : Γ.World => (1:ℝ)*ΦR
      ((Γ.realizedReward ω,Γ.realizedDuration ω),Model.Instance.projectWorld (Fin.castAddEmb N) ω)) =ᵐ[(P.appendIndependent Q).worldLaw π.seedLaw]
      (fun ω => g (Model.Instance.projectWorld (Fin.castAddEmb N) ω)*Γ.realizedReward ω) := by
    filter_upwards [hRanges] with ω hω
    simpa only [one_mul] using congrArg (fun x => g (Model.Instance.projectWorld (Fin.castAddEmb N) ω)*x) (boundedClamp_eq H hω.1)
  have hTTarget : (fun ω : Γ.World => (1:ℝ)*ΦT
      ((Γ.realizedReward ω,Γ.realizedDuration ω),Model.Instance.projectWorld (Fin.castAddEmb N) ω)) =ᵐ[(P.appendIndependent Q).worldLaw π.seedLaw]
      (fun ω => g (Model.Instance.projectWorld (Fin.castAddEmb N) ω)*Γ.realizedDuration ω) := by
    filter_upwards [hRanges] with ω hω
    simpa only [one_mul] using congrArg (fun x => g (Model.Instance.projectWorld (Fin.castAddEmb N) ω)*x) (boundedClamp_eq 1 hω.2)
  exact ⟨⟨hR.1.congr hRTarget,(integral_congr_ae hRTarget).symm.trans (by simpa only [one_mul] using hR.2.2)⟩,
    ⟨hT.1.congr hTTarget,(integral_congr_ae hTTarget).symm.trans (by simpa only [one_mul] using hT.2.2)⟩⟩
end ProphetSecretary.Limiting
