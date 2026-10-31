import ProphetSecretary.LowerBound.Experiment
import ProphetSecretary.Probability.TargetScoreResponse
import ProphetSecretary.Probability.FiniteExperimentInformation

/-!
# The actual finite likelihood experiment and its fixed-policy derivatives

The experiment contains only the finite product laws, scalar weights and
fixed bounded marginal scores. Its information and derivative identities
are proved from the actual likelihood laws. The policy and its independent
auxiliary law are held fixed while the parameter varies.
-/
open MeasureTheory InformationTheory Set
open scoped Classical Topology
namespace ProphetSecretary.LowerBound
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def likelihoodExperiment (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m))
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0) (lams : ℕ → ℝ) : Experiment where
  size := sizes
  law m θ := (P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) θ
  weight := lams

lemma likelihoodExperiment_law_zero (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m))
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0) (lams : ℕ → ℝ) (m : ℕ) :
    (likelihoodExperiment sizes P score hh hb hm lams).law m 0=P m :=
  (P m).likelihoodWidePath_zero_eq (score m) (hh m) (hb m) (hm m)

lemma likelihoodExperiment_gap_deriv (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H : ℝ}
    (hH : 0≤H) (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0) (lams : ℕ → ℝ)
    (hRange : ∀ m, lams m∈Icc (0:ℝ) 1) (m : ℕ) (π : RandomizedPolicy (sizes m)) :
    deriv ((likelihoodExperiment sizes P score hh hb hm lams).baseWeightGap m π) 0=
      π.normalizedScoreResponse (P m) (score m) (lams m) := by
  exact (π.hasDerivAt_normalizedScoreResponse (P m) hH (hCap m) (hRange m) (score m) (hh m) (hb m) (hm m)).deriv

lemma likelihoodExperiment_balance_deriv (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H : ℝ}
    (hH : 0≤H) (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0) (lams : ℕ → ℝ)
    (m : ℕ) (π : RandomizedPolicy (sizes m)) :
    deriv ((likelihoodExperiment sizes P score hh hb hm lams).balanceDifference m π) 0=
      π.targetScoreResponse (P m) (score m) := by
  exact (π.hasDerivAt_targetScoreResponse (P m) hH (hCap m) (score m) (hh m) (hb m) (hm m)).deriv

theorem likelihoodExperiment_information (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {I : ℝ}
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0) (lams : ℕ → ℝ)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    let E := likelihoodExperiment sizes P score hh hb hm lams
    ∀ m k (L : Learner (sizes m) k) t, |t|≤1/4 →
      klDiv (L.transcriptLaw (E.law m t)) (L.transcriptLaw (E.law m (-t)))+
        klDiv (L.transcriptLaw (E.law m (-t))) (L.transcriptLaw (E.law m t))≤
          ENNReal.ofReal ((16*I)*(k:ℝ)*t^2) := by
  have h := (finite_likelihood_information_controls sizes P score hh hb hm hInfo).2.2.2
  dsimp only
  intro m k L t ht
  simpa only [likelihoodExperiment,mul_assoc,mul_left_comm,mul_comm] using h m k L t ht
end ProphetSecretary.LowerBound
