import ProphetSecretary.LowerBound.LikelihoodExperimentResponse
import ProphetSecretary.LowerBound.LikelihoodExperimentTaylor

/-!
# Complete uniform statistical controls for the actual likelihood experiment

Only a common base cap, positive-tail profile, compact interior weights and
centered bounded component scores with bounded total information are inputs.
Every derivative, Taylor and adaptive-information conclusion is proved for
the actual product-law experiment. Base normalization, criticality and the
negative target response are separate properties of a constructed family.
-/
open MeasureTheory InformationTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.LowerBound
open ProphetSecretary.Model ProphetSecretary.Probability

theorem likelihoodExperiment_controls
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H δ I : ℝ}
    (hH : 0≤H) (hδ : 0<δ) (hI : 0≤I)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (L : ℝ → ℝ) (hL : ∀ d, 0<d → 0≤L d) (hTail : ∀ m d, 0<d → (P m).tailCount d≤L d)
    (lams : ℕ → ℝ) (hRange : ∀ m, lams m∈Icc δ (1-δ))
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    let E := likelihoodExperiment sizes P score hh hb hm lams
    let πopt := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
      (hδ.le.trans (hRange m).1) (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])
    (∀ m θ, |θ|≤1/4 → ∀ i, ∀ᵐ x ∂(E.law m θ).law i, x≤H) ∧
    (∀ m, (πopt m).scalarObjective (E.law m 0) (E.weight m) (1-E.weight m)=
      optimalScalarValue (E.law m 0) (E.weight m) (1-E.weight m)) ∧
    (∀ m, (∫ x, completeScore (score m) x ∂(P m).valuesLaw)=0) ∧
    (∀ m, (∫ x, (completeScore (score m) x)^2 ∂(P m).valuesLaw)≤I) ∧
    (∀ m θ, |θ|≤1/4 → (∫ x, |likelihood (score m) θ x-1-θ*completeScore (score m) x|
      ∂(P m).valuesLaw)≤2*θ^2*I) ∧
    (∀ m k (A : Learner (sizes m) k) t, |t|≤1/4 →
      klDiv (A.transcriptLaw (E.law m t)) (A.transcriptLaw (E.law m (-t)))+
        klDiv (A.transcriptLaw (E.law m (-t))) (A.transcriptLaw (E.law m t))≤
          ENNReal.ofReal ((16*I)*(k:ℝ)*t^2)) ∧
    (∀ m (π : RandomizedPolicy (sizes m)) θ, |θ|≤1/4 →
      (|E.baseWeightGap m π θ-E.baseWeightGap m π 0-θ*deriv (E.baseWeightGap m π) 0|≤(4*(H+1)*I)*θ^2) ∧
      (|E.balanceDifference m π θ-E.balanceDifference m π 0-θ*deriv (E.balanceDifference m π) 0|≤(4*(H+1)*I)*θ^2)) ∧
    (∃ ω : ℝ → ℝ, Monotone ω ∧
      (∀ s, 0≤s → 0≤ω s ∧ ω s≤2*Real.sqrt (2*I*(H+1)*(H+1))) ∧ ω 0=0 ∧
      Tendsto ω (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) ∧
      ∀ m (π : RandomizedPolicy (sizes m)),
        |deriv (E.baseWeightGap m π) 0-deriv (E.baseWeightGap m (πopt m)) 0|+
          |deriv (E.balanceDifference m π) 0-deriv (E.balanceDifference m (πopt m)) 0|≤ω (E.scalarRegret m π)) := by
  let E := likelihoodExperiment sizes P score hh hb hm lams
  let πopt := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
    (hδ.le.trans (hRange m).1) (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])
  have hUnit (m) : lams m∈Icc (0:ℝ) 1 := ⟨hδ.le.trans (hRange m).1,by linarith only [(hRange m).2,hδ.le]⟩
  have hRaw := finite_likelihood_information_controls sizes P score hh hb hm hInfo
  refine ⟨?_,?_,hRaw.1,hRaw.2.1,hRaw.2.2.1,?_,?_,?_⟩
  · intro m θ _hθ
    exact (P m).likelihoodWidePath_bounded (score m) (hh m) (hb m) (hm m) θ (hCap m)
  · intro m
    change (πopt m).scalarObjective ((P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) 0) (lams m) (1-lams m)=
      optimalScalarValue ((P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) 0) (lams m) (1-lams m)
    rw [(P m).likelihoodWidePath_zero_eq (score m) (hh m) (hb m) (hm m)]
    exact (P m).valuePolicy_optimal ((P m).integrable_maximum_of_bounded (hCap m)) (hδ.trans_le (hRange m).1)
      (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])
  · exact likelihoodExperiment_information sizes P score hh hb hm lams hInfo
  · exact likelihoodExperiment_taylor sizes P hH hI hCap score hh hb hm lams hUnit hInfo
  · exact likelihoodExperiment_response_stability sizes P hH hδ hI hCap L hL hTail lams hRange score hh hb hm hInfo
end ProphetSecretary.LowerBound
