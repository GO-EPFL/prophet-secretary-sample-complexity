import ProphetSecretary.Statistics.PlannerPrimitiveHeight
import ProphetSecretary.Statistics.ScalarPlannerAccuracy
import ProphetSecretary.Statistics.ScalarPlannerWorkTree

/-!
# Intermediate rational operands of the scalar planner

Finite sums use suffix accumulators. The bounds apply to every suffix,
not only the returned sum, as well as to all averaging powers, the
weighted payoff scan, and the precision search.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

lemma rationalHeight_list_sum_uniform (l : List ℚ) (B : ℕ) (h : ∀ x ∈ l, RationalHeight x B) :
    RationalHeight l.sum (l.length*(B+1)) := by
  induction l with
  | nil => simpa using rationalHeight_zero
  | cons x l ih =>
    have hs := (h x List.mem_cons_self).add (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))
    exact hs.mono (by simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega)

lemma countedFiniteSum_accumulator_height {K : ℕ} (f : Fin K → ℚ × ℕ) (B s : ℕ)
    (h : ∀ i, RationalHeight (f i).1 B) :
    RationalHeight (((List.ofFn f).map Prod.fst).drop s).sum (K*(B+1)) := by
  let l := (List.ofFn f).map Prod.fst
  have hl : l.length = K := by simp [l]
  have hlen : (l.drop s).length ≤ K := by rw [List.length_drop,hl]; exact Nat.sub_le _ _
  apply (rationalHeight_list_sum_uniform (l.drop s) B ?_).mono (Nat.mul_le_mul_right _ hlen)
  intro x hx
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ((List.drop_sublist s l).subset hx)
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hp
  rw [← hi]
  exact h i

lemma countedFourPower_intermediate_height (d j : ℕ) (hj : j ≤ d) :
    RationalHeight (countedFourPower (Value := ℚ) j).1.2 (2*d) := by
  rw [countedFourPower_value]
  exact (rationalHeight_four.pow j).mono (by omega)

lemma countedMultilevelAverage_operands_height (d : ℕ) (f : Fin (4^d) → ℚ × ℕ)
    (B : ℕ) (h : ∀ i, RationalHeight (f i).1 B) :
    (∀ s, RationalHeight (((List.ofFn f).map Prod.fst).drop s).sum (4^d*(B+1))) ∧
      RationalHeight (1/(4:ℚ)^d) (2*d) ∧
      RationalHeight (countedMultilevelAverage d f).1 (4^d*(B+1)+2*d) := by
  have ha := rationalHeight_averageCoefficient d
  have hs := countedFiniteSum_accumulator_height f B 0 h
  refine ⟨fun s => countedFiniteSum_accumulator_height f B s h,ha,?_⟩
  rw [countedMultilevelAverage_value]
  have hSum : RationalHeight (∑ i, (f i).1) (4^d*(B+1)) := by
    simpa only [List.drop_zero,List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hs
  exact (ha.mul hSum).mono (by omega)

lemma countedPlannerExcess_accumulator_height (l : List ℚ) (v : ℚ) (Y P A m s : ℕ)
    (hY : ∀ x ∈ l, RationalHeight x Y) (hm : l.length ≤ m) (hP : m ≤ 2^P)
    (hv : RationalHeight v A) :
    RationalHeight (countedPlannerExcessTotals v (l.drop s)).1.1 (m*(Y+1)+P+A+1) ∧
      RationalHeight (countedPlannerExcessTotals v (l.drop s)).1.2 P := by
  let q := l.drop s
  have hQ : q.length ≤ m := (by rw [List.length_drop]; exact Nat.sub_le _ _ : q.length ≤ l.length).trans hm
  obtain ⟨a,c,he,ha,hc⟩ := countedPlannerExcessTotals_affine q v Y
    (fun x hx => hY x ((List.drop_sublist s l).subset hx))
  have hC := rationalHeight_natCast c P (hc.trans (hQ.trans hP))
  have hL := Nat.mul_le_mul_right (Y+1) hQ
  change RationalHeight (countedPlannerExcessTotals v q).1.1 _ ∧ RationalHeight (countedPlannerExcessTotals v q).1.2 _
  refine ⟨?_,?_⟩
  · rw [he]
    exact (ha.sub (hC.mul hv)).mono (by omega)
  · rw [countedPlannerExcessTotals_value]
    exact rationalHeight_natCast _ _ (List.countP_le_length.trans (hQ.trans hP))

lemma countedQuarterPower_height (d j : ℕ) (hj : j ≤ d) :
    RationalHeight (countedQuarterPower (K := ℚ) j).1 (2*d) := by
  rw [countedQuarterPower_value,one_div_pow]
  exact (rationalHeight_averageCoefficient j).mono (by omega)

lemma scalarPlannerPrecisionRatio_height {β h : ℚ} {B H : ℕ}
    (hβ : RationalHeight β B) (hh : RationalHeight h H) :
    RationalHeight (scalarPlannerPrecisionRatio β h) (2*H+2*B+11) := by
  have hC : RationalHeight (1600:ℚ) 11 := by unfold RationalHeight; decide
  exact ((hh.pow 2).div (hC.mul (hβ.pow 2))).mono (by omega)

end ProphetSecretary.Statistics
