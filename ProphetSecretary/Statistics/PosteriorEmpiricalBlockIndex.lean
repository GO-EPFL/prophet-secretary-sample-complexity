import ProphetSecretary.Statistics.PosteriorEmpiricalLearner
import ProphetSecretary.Model.EmpiricalTrainingBlock

/-!
# Locating the empirical block inside the visible prefix

After a preliminary block of b samples and a pilot block of m samples,
the next m columns form the empirical law. The comparison is an equality
of raw sample callbacks, so it supplies no masked or future value to the
algorithm. A product-law split can then justify its statistical estimate.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n m N : ℕ} [NeZero m]

def empiricalBlockColumn (b m L : ℕ) (h : b+2*m≤L) : Fin m ↪ Fin L where
  toFun j := ⟨b+m+j.val,by omega⟩
  inj' := by intro i j he; apply Fin.ext; have hv := congrArg Fin.val he; dsimp at hv; omega

omit [NeZero m] in
lemma empiricalBlockRead_extend_prefix (N b k : ℕ) (h : b+2*m≤trainingLength N b k)
    (y : Reservoir n (trainingLength N b k)) :
    empiricalBlockRead (empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N))))
        (extendTrainingPrefix n N b k y) =
      (splitTrainingBlock (empiricalBlockColumn b m (trainingLength N b k) h) y).1 := by
  funext i j
  rw [splitTrainingBlock_first]
  have hj : b+m+j.val<trainingLength N b k := by omega
  change (if h' : b+m+j.val<trainingLength N b k then y i ⟨b+m+j.val,h'⟩ else 0)=_
  rw [dif_pos hj]
  rfl

noncomputable def prefixPosteriorScalar (F : FinitePrior n) (N b k : ℕ) (ρ : ℝ → ℝ) :
    Reservoir n (trainingLength N b k) × Unit → ℝ :=
  fun p => F.posteriorEmpiricalScalar N b k ρ (extendTrainingPrefix n N b k p.1)

lemma measurable_prefixPosteriorScalar (F : FinitePrior n) (N b k : ℕ) {ρ : ℝ → ℝ} (hρ : Measurable ρ) :
    Measurable (F.prefixPosteriorScalar N b k ρ) :=
  (F.measurable_posteriorEmpiricalScalar N b k hρ).comp
    ((measurable_extendTrainingPrefix n N b k).comp measurable_fst)

lemma posteriorEmpirical_samplePolicy_eq_block (F : FinitePrior n) (N b k : ℕ)
    (h : b+2*m≤trainingLength N b k) (ρ : ℝ → ℝ) :
    prefixSamplePolicy N b k (F.posteriorEmpiricalPolicy N b k
      (empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))) ρ) =
      empiricalTrainingBlockPolicy (empiricalBlockColumn b m (trainingLength N b k) h)
        (F.prefixPosteriorScalar N b k ρ) := by
  let e := empiricalBlockColumn b m (trainingLength N b k) h
  apply congrArg Policy.mk
  funext p t i x H
  rcases p with ⟨y,r⟩
  change Decidable.decide (0<x ∧ empiricalCapThreshold
      (empiricalBlockRead (empiricalBlockColumn b m (N+1)
        (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))) (extendTrainingPrefix n N b k y))
      (F.posteriorEmpiricalScalar N b k ρ (extendTrainingPrefix n N b k y)) (unseen H) t i≤x) =
    Decidable.decide (0<x ∧ empiricalCapThreshold (trainingBlockSeedEquiv e (y,r)).1
      (F.prefixPosteriorScalar N b k ρ ((trainingBlockSeedEquiv e).symm (trainingBlockSeedEquiv e (y,r))))
      (unseen H) t i≤x)
  rw [MeasurableEquiv.symm_apply_apply,empiricalBlockRead_extend_prefix N b k h]
  rfl

theorem posteriorEmpiricalLearner_eq_block (F : FinitePrior n) (N b k : ℕ)
    (h : b+2*m≤trainingLength N b k) (ρ : ℝ → ℝ) (hρ : Measurable ρ) :
    F.posteriorEmpiricalLearner N b k
      (empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))) ρ hρ =
      Learner.empiricalTrainingBlock (Measure.dirac ())
        (empiricalBlockColumn b m (trainingLength N b k) h)
        (F.prefixPosteriorScalar N b k ρ) (F.measurable_prefixPosteriorScalar N b k hρ) := by
  unfold posteriorEmpiricalLearner prefixLearner Learner.empiricalTrainingBlock
  congr 1
  exact F.posteriorEmpirical_samplePolicy_eq_block N b k h ρ

end ProphetSecretary.Statistics.FinitePrior
