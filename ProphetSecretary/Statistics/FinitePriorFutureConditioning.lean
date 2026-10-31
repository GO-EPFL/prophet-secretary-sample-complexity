import ProphetSecretary.Statistics.FinitePriorTrainingSplit
import ProphetSecretary.Statistics.FinitePriorPosteriorWeights
import ProphetSecretary.Probability.ConditionalMapPullback

/-!
# Actual posterior future law after preliminary observations

After the h preliminary training rounds, the d further training rounds and
distinct ONLINE vector retain their product-instance law conditional on each
hidden prior atom. Conditioning on the actual observed preliminary prefix mixes
these future laws with the actual posterior atom weights. The equivalence and
information sigma algebra are proved, not supplied as a restart interface.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model ProphetSecretary.Probability
variable {n : ℕ}

/-- Conditional expectation of any bounded measurable analytical payoff of the
hidden atom, preliminary data, and whole future block. It does not expose the
future block to a training protocol or online policy. -/
theorem future_condExp_eq_posterior_mixture (F : FinitePrior n) (h d : ℕ)
    {f : Fin F.size × (((Fin n × Fin h) → ℝ) × ((Fin n × Fin (d+1)) → ℝ)) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC0 : 0≤C) (hBound : ∀ w, ‖f w‖≤C) :
    (F.law (h+d))[(fun ω => f (F.splitBaseTraining h d ω))|F.dataSigma (h+d) 0 h] =ᵐ[F.law (h+d)]
      (fun ω => ∑ θ : Fin F.size,
        (∫ y, f (θ,((F.splitBaseTraining h d ω).2.1,y)) ∂(F.offerInstance θ).trainingCoordinateLaw (d+1))*
          F.atomPosterior (h+d) 0 h θ ω) := by
  let T := F.splitBaseTraining h d
  let ρ := finiteMixtureProductLaw F.weight (fun θ => (F.offerInstance θ).trainingCoordinateLaw h)
    (fun θ => (F.offerInstance θ).trainingCoordinateLaw (d+1))
  have hMP := F.splitBaseTraining_measurePreserving h d
  have hm : mixturePastSigma (Θ:=Fin F.size) (A:=(Fin n × Fin h) → ℝ) (B:=(Fin n × Fin (d+1)) → ℝ) ≤ (inferInstance : MeasurableSpace (Fin F.size × (((Fin n × Fin h) → ℝ) × ((Fin n × Fin (d+1)) → ℝ)))) :=
    mixturePastSigma_le
  have hfI : Integrable f ρ := integrable_of_pointwise_norm_bound ρ hf hBound
  have hPull := condExp_pullback_measurePreserving (F.law (h+d)) ρ hMP hm hfI
  rw [←F.dataSigma_eq_split_past] at hPull
  have hCE := condExp_finiteMixtureProductLaw F.weight
    (fun θ => (F.offerInstance θ).trainingCoordinateLaw h)
    (fun θ => (F.offerInstance θ).trainingCoordinateLaw (d+1)) hf hC0 hBound
  have hCEPull := hMP.quasiMeasurePreserving.ae hCE
  have hAtom (θ : Fin F.size) :
      (fun ω => ρ[mixtureAtomIndicator θ|mixturePastSigma] (T ω)) =ᵐ[F.law (h+d)] F.atomPosterior (h+d) 0 h θ := by
    have hIm : Measurable (mixtureAtomIndicator (A:=(Fin n × Fin h) → ℝ) (B:=(Fin n × Fin (d+1)) → ℝ) θ) := by
      convert (measurable_of_finite (fun t : Fin F.size => if t=θ then (1:ℝ) else 0)).comp
        (measurable_fst : Measurable (Prod.fst : Fin F.size × (((Fin n × Fin h) → ℝ) × ((Fin n × Fin (d+1)) → ℝ)) → Fin F.size)) using 1
      funext w
      simp only [Function.comp_def]
      unfold mixtureAtomIndicator
      split_ifs <;> rfl
    have hIB (w : Fin F.size × (((Fin n × Fin h) → ℝ) × ((Fin n × Fin (d+1)) → ℝ))) :
        ‖mixtureAtomIndicator θ w‖≤1 := by
      unfold mixtureAtomIndicator
      split_ifs <;> norm_num
    have hAI := integrable_of_pointwise_norm_bound ρ hIm hIB
    have hTransport := condExp_pullback_measurePreserving (F.law (h+d)) ρ hMP hm hAI
    rw [←F.dataSigma_eq_split_past] at hTransport
    have hEq : (fun ω => mixtureAtomIndicator θ (F.splitBaseTraining h d ω))=F.atomIndicator (N:=h+d) θ := by
      funext ω
      have hFirst : (F.splitBaseTraining h d ω).1=ω.1 := rfl
      unfold mixtureAtomIndicator atomIndicator
      rw [hFirst]
      split_ifs <;> rfl
    rw [hEq] at hTransport
    exact hTransport
  have hAll := ae_all_iff.mpr hAtom
  filter_upwards [hPull,hCEPull,hAll] with ω hF hCEω hA
  rw [←hF,hCEω]
  exact Finset.sum_congr rfl fun θ _ => congrArg
    ((∫ y, f (θ,((F.splitBaseTraining h d ω).2.1,y)) ∂(F.offerInstance θ).trainingCoordinateLaw (d+1))*·) (hA θ)

end ProphetSecretary.Statistics.FinitePrior
