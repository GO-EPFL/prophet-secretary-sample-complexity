import ProphetSecretary.Probability.FiniteExperimentInformation
import ProphetSecretary.Probability.FiniteExperimentTaylor

/-!
# Dimension-independent information and likelihood estimates

This is the estimate in `lem:score-information`, with explicit constants.
The direct score constructions prove its centering, unit bounds and uniform
information hypothesis. A fixed independent auxiliary law can include clocks,
policy randomness and all observations not changed by the likelihood tilt.
The complete-vector score remains an analytical random variable.
-/

open MeasureTheory InformationTheory Set
open scoped Classical
namespace ProphetSecretary.LowerBound
open ProphetSecretary.Model ProphetSecretary.Probability

theorem finite_score_information {Aux : Type*} [MeasurableSpace Aux]
    (ν : Measure Aux) [IsProbabilityMeasure ν]
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {I : ℝ}
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    let Q := fun m θ => (P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ
    (∀ m, (∫ x, completeScore (score m) x ∂(P m).valuesLaw)=0) ∧
    (∀ m, (∫ x, (completeScore (score m) x)^2 ∂(P m).valuesLaw)≤I) ∧
    (∀ m θ, |θ|≤1/4 →
      (∫ x, |likelihood (score m) θ x-1-θ*completeScore (score m) x| ∂(P m).valuesLaw)≤2*θ^2*I) ∧
    (∀ m (G : (Fin (sizes m) → ℝ) × Aux → ℝ), Measurable G →
      ∀ B : ℝ, 0≤B → (∀ᵐ z ∂(P m).valuesLaw.prod ν, |G z|≤B) →
      ∀ θ : ℝ, |θ|≤1/4 →
        |(∫ z, G z ∂(Q m θ).valuesLaw.prod ν)-(∫ z, G z ∂(P m).valuesLaw.prod ν)-
          θ*(∫ z, G z*completeScore (score m) z.1 ∂(P m).valuesLaw.prod ν)|≤2*B*θ^2*I) ∧
    ∀ m k (A : Learner (sizes m) k) t, |t|≤1/4 →
      klDiv (A.transcriptLaw (Q m t)) (A.transcriptLaw (Q m (-t)))+
        klDiv (A.transcriptLaw (Q m (-t))) (A.transcriptLaw (Q m t))≤
          ENNReal.ofReal (16*(k : ℝ)*t^2*I) := by
  have h := finite_likelihood_information_controls sizes P score hh hb hm hInfo
  refine ⟨h.1,h.2.1,h.2.2.1,?_,h.2.2.2⟩
  intro m G hG B hB hBound θ hθ
  have hQ : ((P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ).valuesLaw=
      productTiltLaw (P m).law (score m) θ := by
    rw [(P m).likelihoodWidePath_eq_quarter (score m) (hh m) (hb m) (hm m) hθ,
      (P m).likelihoodPath_of_mem (score m) (hh m) (hb m) (hm m) hθ]
    rfl
  dsimp only
  rw [hQ]
  exact (fixedPayoff_law_taylor_bound_prod (P m).law ν (score m) (hh m) (hb m) (hm m)
    G hG hB hBound hθ).trans (mul_le_mul_of_nonneg_left (hInfo m) (by positivity))

end ProphetSecretary.LowerBound
