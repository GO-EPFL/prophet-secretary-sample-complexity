import ProphetSecretary.Limiting.HybridZeroSimulation
import ProphetSecretary.Limiting.IndependentAppend
import ProphetSecretary.Limiting.HybridFiniteCutoffEvaluation
import ProphetSecretary.Model.ScoreProjection
import ProphetSecretary.Model.ScalarObjectiveBounds
import ProphetSecretary.Model.Continuation

/-!
# Causal coarse policies on a direct finite approximation

The identity injection retains the first K individual variables and every
virtual variable. Other individual identities may be observed and ignored.
The projection uses a fixed identity map and the original strict histories;
it reveals no future observations or construction labels.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
variable {K n N : ℕ}

def directCoarseEmbedding (K n N : ℕ) (hKn : K≤n) : Fin (K+N) ↪ Fin (n+N) :=
  (HybridZeroSimulation.keepEmbedding K (n-K) N).toEmbedding.trans
    (finCongr (show K+(n-K)+N=n+N by omega)).toEmbedding

lemma directCoarseEmbedding_left (hKn : K≤n) (i : Fin K) :
    directCoarseEmbedding K n N hKn (i.castAdd N)=(Fin.castLE hKn i).castAdd N := by
  apply Fin.ext
  change (HybridZeroSimulation.keepEmbedding K (n-K) N (i.castAdd N)).val=i.val
  rw [HybridZeroSimulation.keepEmbedding_left]
  rfl

lemma directCoarseEmbedding_right (hKn : K≤n) (j : Fin N) :
    directCoarseEmbedding K n N hKn (j.natAdd K)=j.natAdd n := by
  apply Fin.ext
  change (HybridZeroSimulation.keepEmbedding K (n-K) N (j.natAdd K)).val=n+j.val
  rw [HybridZeroSimulation.keepEmbedding_right]
  simp only [Fin.val_natAdd]
  omega

lemma directCoarse_restricted_instance (P : Model.Instance n) (Q : Model.Instance N) (hKn : K≤n) :
    (P.appendIndependent Q).restrictBy (directCoarseEmbedding K n N hKn)=
      (P.restrictBy (Fin.castLEEmb hKn)).appendIndependent Q := by
  apply Model.Instance.eq_of_law_eq
  funext j
  change (P.appendIndependent Q).law (directCoarseEmbedding K n N hKn j)=_
  induction j using Fin.addCases with
  | left i =>
    rw [directCoarseEmbedding_left,Model.Instance.appendIndependent_law_left,Model.Instance.appendIndependent_law_left]
    rfl
  | right j =>
    rw [directCoarseEmbedding_right,Model.Instance.appendIndependent_law_right]
    simp only [Model.Instance.appendIndependent_law_right]

noncomputable def directCoarsePolicy (n N : ℕ) (π : RandomizedHybridPolicy K) (d : ℝ) : Model.RandomizedPolicy (n+N) :=
  if h : K≤n then (π.finiteCutoffEvaluation N d).ignoreExtras (directCoarseEmbedding K n N h)
    else Model.RandomizedPolicy.waiting (n+N)

lemma directCoarsePolicy_expectedReward (P : Model.Instance n) (Q : Model.Instance N)
    (π : RandomizedHybridPolicy K) (d : ℝ) (hKn : K≤n) :
    (directCoarsePolicy n N π d).expectedReward (P.appendIndependent Q)=
      (π.finiteCutoffEvaluation N d).expectedReward ((P.restrictBy (Fin.castLEEmb hKn)).appendIndependent Q) := by
  have hγ : directCoarsePolicy n N π d=(π.finiteCutoffEvaluation N d).ignoreExtras (directCoarseEmbedding K n N hKn) :=
    dif_pos hKn
  exact (congrArg (fun ρ : Model.RandomizedPolicy (n+N) => ρ.expectedReward (P.appendIndependent Q)) hγ).trans
    (((π.finiteCutoffEvaluation N d).ignoreExtras_expectedReward (P.appendIndependent Q) (directCoarseEmbedding K n N hKn)).trans
      (congrArg (fun A : Model.Instance (K+N) => (π.finiteCutoffEvaluation N d).expectedReward A)
        (directCoarse_restricted_instance P Q hKn)))

lemma directCoarsePolicy_expectedDuration (P : Model.Instance n) (Q : Model.Instance N)
    (π : RandomizedHybridPolicy K) (d : ℝ) (hKn : K≤n) :
    (directCoarsePolicy n N π d).expectedDuration (P.appendIndependent Q)=
      (π.finiteCutoffEvaluation N d).expectedDuration ((P.restrictBy (Fin.castLEEmb hKn)).appendIndependent Q) := by
  have hγ : directCoarsePolicy n N π d=(π.finiteCutoffEvaluation N d).ignoreExtras (directCoarseEmbedding K n N hKn) :=
    dif_pos hKn
  exact (congrArg (fun ρ : Model.RandomizedPolicy (n+N) => ρ.expectedDuration (P.appendIndependent Q)) hγ).trans
    (((π.finiteCutoffEvaluation N d).ignoreExtras_expectedDuration (P.appendIndependent Q) (directCoarseEmbedding K n N hKn)).trans
      (congrArg (fun A : Model.Instance (K+N) => (π.finiteCutoffEvaluation N d).expectedDuration A)
        (directCoarse_restricted_instance P Q hKn)))
end ProphetSecretary.Limiting
