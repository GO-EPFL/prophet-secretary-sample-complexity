import ProphetSecretary.Limiting.HybridFiniteCutoffEvaluation
import ProphetSecretary.Limiting.BandObservableMoments
import ProphetSecretary.Model.Restriction

/-!
# Complete virtual-score expectations of the finite cutoff execution

The actual concatenated instance and the independent virtual/retained world
are related by the constructed product map. Any integrable complete virtual
score can multiply a bounded measurable outcome/data test. Neither the score
nor the complete point measure is passed to a policy callback.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n N : ℕ}

lemma RandomizedHybridPolicy.finiteCutoffEvaluation_scored_observables
    (π : RandomizedHybridPolicy n) (P : Model.Instance n) (Q : Model.Instance N) (d : ℝ)
    (s : (Fin N → ℝ) → ℝ) (hs : Measurable s) (hsInt : Integrable s Q.valuesLaw)
    (Φ : (ℝ × ℝ) × Model.World n π.Seed → ℝ) (hΦ : Measurable Φ)
    {D : ℝ} (hb : ∀ z, ‖Φ z‖≤D) :
    let Γ := π.finiteCutoffEvaluation N d
    let T := fun ω : Γ.World => s (fun j => ω.1 (j.natAdd n))*
      Φ ((Γ.realizedReward ω,Γ.realizedDuration ω),Model.Instance.projectWorld (Fin.castAddEmb N) ω)
    let G := fun q : (Measure Point) × Model.World n π.Seed => Φ
      ((π.rule.observableReward 0 (ProphetSecretary.Probability.finiteMeasureOrZero q.1,q.2),
        π.rule.observableDuration (ProphetSecretary.Probability.finiteMeasureOrZero q.1,q.2)),q.2)
    let X := fun ω : Model.World N (Model.World n π.Seed) =>
      (thresholdedOfferCountingMeasure d (fun j => (ω.2.1 j,ω.1 j)),ω.2.2)
    Integrable T ((P.appendIndependent Q).worldLaw π.seedLaw) ∧
      Integrable (fun ω => s ω.1*G (X ω)) (Q.worldLaw (P.worldLaw π.seedLaw)) ∧
      (∫ ω, T ω ∂(P.appendIndependent Q).worldLaw π.seedLaw)=
        ∫ ω, s ω.1*G (X ω) ∂Q.worldLaw (P.worldLaw π.seedLaw) := by
  let Γ := π.finiteCutoffEvaluation N d
  let T := fun ω : Γ.World => s (fun j => ω.1 (j.natAdd n))*
    Φ ((Γ.realizedReward ω,Γ.realizedDuration ω),Model.Instance.projectWorld (Fin.castAddEmb N) ω)
  let G := fun q : (Measure Point) × Model.World n π.Seed => Φ
    ((π.rule.observableReward 0 (ProphetSecretary.Probability.finiteMeasureOrZero q.1,q.2),
      π.rule.observableDuration (ProphetSecretary.Probability.finiteMeasureOrZero q.1,q.2)),q.2)
  let X := fun ω : Model.World N (Model.World n π.Seed) =>
    (thresholdedOfferCountingMeasure d (fun j => (ω.2.1 j,ω.1 j)),ω.2.2)
  let A := Model.World N (Model.World n π.Seed)
  let ν := Q.worldLaw (P.worldLaw π.seedLaw)
  let F : A → Γ.World := fun ω =>
    (combinedValues ω.2.2.1 (fun j => (ω.2.1 j,ω.1 j)),
      (combinedClocks ω.2.2.2.1 (fun j => (ω.2.1 j,ω.1 j)),ω.2.2.2.2))
  have hPairs := retainedPairs_measurePreserving Q (P.worldLaw π.seedLaw)
  have hF : MeasurePreserving F ν ((P.appendIndependent Q).worldLaw π.seedLaw) :=
    (generalFiniteArrayWorld_measurePreserving P Q π.seedLaw).comp hPairs
  have hX : Measurable X := (thresholdedPointWorld_measurePreserving Q (P.worldLaw π.seedLaw) d).measurable
  have hObs : Measurable (fun q : (Measure Point) × Model.World n π.Seed =>
      (ProphetSecretary.Probability.finiteMeasureOrZero q.1,q.2)) :=
    (ProphetSecretary.Probability.measurable_finiteMeasureOrZero.comp measurable_fst).prodMk measurable_snd
  have hG : Measurable G := hΦ.comp
    ((((π.rule.measurable_observableReward π.measurable_rule 0).comp hObs).prodMk
      ((π.rule.measurable_observableDuration π.measurable_rule).comp hObs)).prodMk measurable_snd)
  have hTail : Measurable (fun ω : Γ.World => fun j : Fin N => ω.1 (j.natAdd n)) :=
    measurable_pi_lambda _ (fun j => (measurable_pi_apply (j.natAdd n)).comp measurable_fst)
  have hRet : Measurable (fun ω : Γ.World => Model.Instance.projectWorld (Fin.castAddEmb N) ω) :=
    ((P.appendIndependent Q).projectWorld_measurePreserving (Fin.castAddEmb N) π.seedLaw).measurable
  have hT : Measurable T := (hs.comp hTail).mul
    (hΦ.comp ((Γ.measurable_realizedReward.prodMk Γ.measurable_realizedDuration).prodMk hRet))
  have hScoreInt : Integrable (fun ω : A => s ω.1) ν :=
    (measurePreserving_fst (μ := Q.valuesLaw) (ν := (Model.Instance.clocksLaw N).prod (P.worldLaw π.seedLaw))).integrable_comp_of_integrable hsInt
  have hSourceInt : Integrable (fun ω : A => s ω.1*G (X ω)) ν := by
    simpa only [Function.comp_def,mul_comm] using hScoreInt.bdd_mul (hG.comp hX).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => hb _))
  have hEq : T ∘ F =ᵐ[ν] (fun ω : A => s ω.1*G (X ω)) := by
    filter_upwards [hPairs.quasiMeasurePreserving.ae
      (π.finiteCutoffEvaluation_payoffs_eq_observable_ae P Q d)] with ω hPay
    have hTailEq : (fun j : Fin N => (F ω).1 (j.natAdd n))=ω.1 := by
      funext j
      simp only [F,combinedValues,Fin.addCases_right]
    have hRetEq : Model.Instance.projectWorld (Fin.castAddEmb N) (F ω)=ω.2.2 := by
      apply Prod.ext
      · funext i
        simp only [Model.Instance.projectWorld,F,Function.comp_def,Fin.castAddEmb_apply,combinedValues,Fin.addCases_left]
      · apply Prod.ext
        · funext i
          simp only [Model.Instance.projectWorld,F,Function.comp_def,Fin.castAddEmb_apply,combinedClocks,Fin.addCases_left]
        · rfl
    change s (fun j => (F ω).1 (j.natAdd n))*
      Φ ((Γ.realizedReward (F ω),Γ.realizedDuration (F ω)),Model.Instance.projectWorld (Fin.castAddEmb N) (F ω))=_
    have hOut : ((Γ.realizedReward (F ω),Γ.realizedDuration (F ω)),
        Model.Instance.projectWorld (Fin.castAddEmb N) (F ω))=
        ((π.rule.observableReward 0 (finiteCutoffObserver d ((fun j => (ω.2.1 j,ω.1 j)),ω.2.2)),
          π.rule.observableDuration (finiteCutoffObserver d ((fun j => (ω.2.1 j,ω.1 j)),ω.2.2))),ω.2.2) :=
      Prod.ext (Prod.ext hPay.1 hPay.2) hRetEq
    exact congrArg₂ (fun a b : ℝ => a*b) (congrArg s hTailEq) (congrArg Φ hOut)
  have hPullInt : Integrable (T ∘ F) ν := hSourceInt.congr hEq.symm
  have hTargetInt : Integrable T ((P.appendIndependent Q).worldLaw π.seedLaw) := by
    rw [← hF.map_eq]
    exact (integrable_map_measure hT.aestronglyMeasurable hF.measurable.aemeasurable).mpr hPullInt
  exact ⟨hTargetInt,hSourceInt,(hF.hasLaw.integral_comp hT.aestronglyMeasurable).symm.trans (integral_congr_ae hEq)⟩
end ProphetSecretary.Limiting
