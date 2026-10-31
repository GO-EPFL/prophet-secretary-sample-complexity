import ProphetSecretary.Probability.NormalizedScoreResponse
import ProphetSecretary.Probability.LikelihoodInformation

/-!
# Uniform information and complete-likelihood remainders for finite experiments

The score array is indexed by the actual finite marginals. Its complete score
has the proved product variance. Adaptive training is an actual observation
of an independent hard-budget reservoir, and therefore satisfies the same
dimension-independent information bound after data processing.
-/
open MeasureTheory InformationTheory Set
open scoped Classical Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability

theorem finite_likelihood_information_controls
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {I : ℝ}
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    let Q := fun m θ => (P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ
    (∀ m, (∫ x, completeScore (score m) x ∂(P m).valuesLaw)=0) ∧
    (∀ m, (∫ x, (completeScore (score m) x)^2 ∂(P m).valuesLaw)≤I) ∧
    (∀ m θ, |θ|≤1/4 → (∫ x, |likelihood (score m) θ x-1-θ*completeScore (score m) x|
      ∂(P m).valuesLaw)≤2*θ^2*I) ∧
    (∀ m k (L : Learner (sizes m) k) t, |t|≤1/4 →
      klDiv (L.transcriptLaw (Q m t)) (L.transcriptLaw (Q m (-t)))+
        klDiv (L.transcriptLaw (Q m (-t))) (L.transcriptLaw (Q m t))≤ENNReal.ofReal (16*(k:ℝ)*t^2*I)) := by
  let Q := fun m θ => (P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ
  have hQ (m θ) (hθ : |θ|≤1/4) : Q m θ=(P m).likelihoodTilt (score m) (hh m) (hb m) (hm m) θ hθ := by
    change (P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ=_
    rw [(P m).likelihoodWidePath_eq_quarter (score m) (hh m) (hb m) (hm m) hθ,
      (P m).likelihoodPath_of_mem (score m) (hh m) (hb m) (hm m) hθ]
  refine ⟨?_,?_,?_,?_⟩
  · intro m
    exact completeScore_mean (P m).law (score m) (hh m) (hb m) (hm m)
  · intro m
    exact (completeScore_secondMoment (P m).law (score m) (hh m) (hb m) (hm m)).trans_le (hInfo m)
  · intro m θ hθ
    exact (likelihood_L1_remainder_bound (P m).law (score m) (hh m) (hb m) (hm m) hθ).trans
      (mul_le_mul_of_nonneg_left (hInfo m) (by positivity))
  · intro m k L t ht
    have hNeg : |-t|≤1/4 := by simpa only [abs_neg] using ht
    change klDiv (L.transcriptLaw (Q m t)) (L.transcriptLaw (Q m (-t)))+
      klDiv (L.transcriptLaw (Q m (-t))) (L.transcriptLaw (Q m t))≤_
    rw [hQ m t ht,hQ m (-t) hNeg]
    exact (L.symmetric_transcript_tilt_klDiv_le (P m) (score m) (hh m) (hb m) (hm m) ht).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hInfo m) (by positivity)))
end ProphetSecretary.Model
