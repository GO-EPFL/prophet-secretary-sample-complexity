import ProphetSecretary.Statistics.PlannerFairSeed
import ProphetSecretary.Analysis.ArithmeticExpressionMap

/-!
# Exact changes of scalar storage in the sampler

All branches of the counted sampler are determined by comparisons and
the fixed label order. An ordered field embedding preserves them.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ArithmeticExpression

variable {n : ℕ} {K L : Type*} [Field K] [Field L] [LinearOrder K] [LinearOrder L]

def plannerListOutputMap (f : K → L) (o : PlannerListOutput n K) : PlannerListOutput n L :=
  (o.1,f o.2.1,o.2.2)

variable (f : K →+* L) (hf : StrictMono f)
include hf

lemma arithmeticGeneratedMinimumScan_valueMap {α ι : Type*} [LinearOrder α]
    (l : List α) (g : α → ArithmeticExpression ι × ℕ) (x : ι → K) (u : K) (a : α) :
    arithmeticGeneratedMinimumScan l g (fun i => f (x i)) (f u) a = arithmeticGeneratedMinimumScan l g x u a := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have h : f u < eval (fun j => f (x j)) (g i).1 ↔ u < eval x (g i).1 := by
      rw [← eval_map_value f hf,hf.lt_iff_lt]
    simp only [arithmeticGeneratedMinimumScan,ih,h]

lemma countedPlannerFirstChoice_valueMap (l : List (Fin n)) (a : Fin n) (p : Fin n → K) (u : K) :
    countedPlannerFirstChoice l a (fun i => f (p i)) (f u) = countedPlannerFirstChoice l a p u :=
  arithmeticGeneratedMinimumScan_valueMap f hf l (countedPlannerFirstPrefix l) p u a

lemma countedPlannerUniformIdentity_valueMap (l : List (Fin n)) (a : Fin n) (u : K) :
    countedPlannerUniformIdentity l a (f u) = countedPlannerUniformIdentity l a u := by
  simpa only [countedPlannerUniformIdentity,map_zero] using
    arithmeticGeneratedMinimumScan_valueMap f hf l (countedPlannerUniformPrefix l) (fun _ : Fin n => 0) u a

lemma countedPlannerFirstCoins_valueMap (l : List (Fin n)) (p : Fin n → K) (k : Fin n) (u : Fin n → K) :
    countedPlannerFirstCoins l (fun i => f (p i)) k (fun i => f (u i)) = countedPlannerFirstCoins l p k u := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have h : f (u i) ≤ eval (fun j => f (p j)) (plannerProbabilityExpression i) ↔
        u i ≤ eval p (plannerProbabilityExpression i) := by
      rw [← eval_map_value f hf,hf.le_iff_le]
    simp only [countedPlannerFirstCoins,ih,h]

lemma countedPlannerFraction_valueMap (l : List (Fin n)) (u : Fin n → K) :
    countedPlannerFraction l (fun i => f (u i)) =
      (f (countedPlannerFraction l u).1,(countedPlannerFraction l u).2) := by
  unfold countedPlannerFraction
  rw [eval_map_value f hf]

lemma countedPlannerTailCoins_valueMap (l D : List (Fin n)) (s : K) (u : Fin n → K) :
    countedPlannerTailCoins l D (f s) (fun i => f (u i)) = countedPlannerTailCoins l D s u := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [countedPlannerTailCoins,ih,hf.le_iff_le]

lemma countedPlannerFirstStage_valueMap (l : List (Fin n)) (a : Fin n) (p : Fin n → K)
    (s : K × (Fin n → K)) :
    countedPlannerFirstStage l a (fun i => f (p i)) (f s.1,fun i => f (s.2 i)) =
      countedPlannerFirstStage l a p s := by
  simp only [countedPlannerFirstStage,countedPlannerFirstChoice_valueMap f hf,countedPlannerFirstCoins_valueMap f hf]

theorem countedPlannerUniformSampler_valueMap (l : List (Fin n)) (p : Fin n → K)
    (s : PlannerFieldSeed n K) :
    countedPlannerUniformSampler l (fun i => f (p i)) (plannerMapSeed f s) =
      (plannerListOutputMap f (countedPlannerUniformSampler l p s).1,(countedPlannerUniformSampler l p s).2) := by
  cases l with
  | nil => simp [countedPlannerUniformSampler,plannerListOutputMap]
  | cons a l =>
    simp only [countedPlannerUniformSampler,countedPlannerUniformSamplerBody,plannerMapSeed,
      countedPlannerFirstStage_valueMap f hf,countedPlannerUniformIdentity_valueMap f hf,
      countedPlannerFraction_valueMap f hf,countedPlannerTailCoins_valueMap f hf,plannerListOutputMap]

end ProphetSecretary.Statistics
