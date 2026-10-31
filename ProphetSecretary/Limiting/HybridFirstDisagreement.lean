import ProphetSecretary.Limiting.HybridLossProbability
import ProphetSecretary.Stability.FirstDisagreement

/-!
# First disagreement with actual hybrid continuation thresholds

A first disagreement before the final window either has positive candidate
value near the actual Bellman boundary or incurs a large reached loss.
This is pathwise for arbitrary competing causal policies; Markov structure
is used only for the canonical comparison rule.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n N : ℕ} {Seed : Type*}

lemma FiniteIntensityHybridInstance.finiteContinuationAtArrival_duration_lower
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 < w)
    (x u : Fin (n+N) → ℝ) (k : Fin (n+N)) :
    c*(remainingTime (u k) : ℝ) ≤ B.finiteContinuationAtArrival w c x u k := by
  induction k using Fin.addCases with
  | left i =>
    simp only [FiniteIntensityHybridInstance.finiteContinuationAtArrival,finiteHybridThreshold,Fin.addCases_left]
    rw [B.valueHybridThreshold_mul_eq hw c]
    exact FiniteIntensityHybridInstance.durationReward_le_optimalScalarValue _ hw.le
  | right j =>
    simp only [FiniteIntensityHybridInstance.finiteContinuationAtArrival,finiteHybridThreshold,Fin.addCases_right]
    rw [B.valueHybridThreshold_mul_eq hw c]
    exact FiniteIntensityHybridInstance.durationReward_le_optimalScalarValue _ hw.le

lemma HybridRule.disagreementValueLoss_eq_absGap (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) {w : ℝ} (hw : 0 < w) (c : ℝ)
    (v : HybridWorld n Seed) (k : Fin (n+v.1.1))
    (hdiff : (π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ
      (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k ≠
      ((B.valueRule w c).asFinitePolicy v.1.1).action () Finset.univ
        (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k) :
    π.arrivalValueLoss B w c v k =
      |w*combinedValues v.2.1 v.1.2 k-B.finiteContinuationAtArrival w c
        (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k| := by
  let x := combinedValues v.2.1 v.1.2
  let u := combinedClocks v.2.2.1 v.1.2
  let V := B.finiteContinuationAtArrival w c x u k
  let ρ := (B.valueRule w c).asFinitePolicy v.1.1
  have hρ : ρ.action () Finset.univ x u k = true ↔ V ≤ w*x k := by
    dsimp only [ρ,FiniteIntensityHybridInstance.valueRule]
    rw [hybridThresholdRule_asFinitePolicy]
    change decide (finiteHybridThreshold (B.valueHybridThreshold w c) v.1.1 ()
      (Model.unseen (Model.history Finset.univ x u (u k))) (u k) k ≤ x k) = true ↔ _
    rw [decide_eq_true_eq]
    change _ ↔ w*_ ≤ w*x k
    exact (mul_le_mul_iff_right₀ hw).symm
  change (π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ x u k ≠ ρ.action () Finset.univ x u k at hdiff
  change max (w*x k) V-(if (π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ x u k = true then w*x k else V) = |w*x k-V|
  by_cases h : V ≤ w*x k
  · have hnot : ¬(π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ x u k = true :=
      fun ha => hdiff (ha.trans (hρ.mpr h).symm)
    rw [if_neg hnot,max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
  · have hf : ρ.action () Finset.univ x u k = false := by
      cases ha : ρ.action () Finset.univ x u k <;> simp_all
    have ht : (π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ x u k = true := by
      cases ha : (π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ x u k <;> simp_all
    rw [if_pos ht,max_eq_right (le_of_not_ge h),abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
    ring

def HybridRule.earlyValueDifference (π : HybridRule n Seed) (B : FiniteIntensityHybridInstance n)
    (w c window : ℝ) : Set (HybridWorld n Seed) :=
  {v | (π.asFinitePolicy v.1.1).EarlyOutcomeDifference ((B.valueRule w c).asFinitePolicy v.1.1)
    v.2.2.2 () (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) (1-window)}

def FiniteIntensityHybridInstance.positiveValueBand (B : FiniteIntensityHybridInstance n)
    {Seed : Type*} (w c b e : ℝ) : Set (HybridWorld n Seed) :=
  {v | ∃ k : Fin (n+v.1.1), b ≤ combinedValues v.2.1 v.1.2 k ∧
    |w*combinedValues v.2.1 v.1.2 k-B.finiteContinuationAtArrival w c
      (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k| ≤ e}

lemma HybridRule.earlyValueDifference_loss_or_boundary (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) {w c b e : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) (he : e ≤ w*b/4)
    (v : HybridWorld n Seed) (hclock : Function.Injective (combinedClocks v.2.2.1 v.1.2))
    (hEarly : v ∈ π.earlyValueDifference B w c (2*w*b/c)) :
    e ≤ π.reachedValueLoss B w c v ∨ v ∈ B.positiveValueBand w c b e := by
  let x := combinedValues v.2.1 v.1.2
  let u := combinedClocks v.2.2.1 v.1.2
  let window := 2*w*b/c
  have hwindow : 0 ≤ window := by dsimp only [window]; positivity
  obtain ⟨k,huk,hr,_hρr,hact⟩ := (π.asFinitePolicy v.1.1).earlyOutcomeDifference_witness
    ((B.valueRule w c).asFinitePolicy v.1.1) v.2.2.2 () x u hclock
    (show 1-window ≤ 1 by linarith) hEarly
  have hLoss := π.disagreementValueLoss_eq_absGap B hw c v k hact
  have hSum := π.arrivalValueLoss_le_reachedValueLoss B w c v k hr
  by_cases hx : b ≤ x k
  · by_cases hg : |w*x k-B.finiteContinuationAtArrival w c x u k| ≤ e
    · exact Or.inr ⟨k,hx,hg⟩
    · exact Or.inl ((le_of_lt (lt_of_not_ge hg)).trans (hLoss.symm.le.trans hSum))
  · have hsmall : w*x k < w*b := mul_lt_mul_of_pos_left (lt_of_not_ge hx) hw
    have hphysical : window < 1-u k := by linarith
    have hmul := mul_lt_mul_of_pos_left hphysical hc
    have heq : c*window = 2*w*b := by dsimp only [window]; field_simp
    rw [heq] at hmul
    have ht : u k ≤ 1 := by linarith
    have hwait := B.finiteContinuationAtArrival_duration_lower (c := c) hw x u k
    rw [coe_remainingTime ht] at hwait
    have hcont : 2*w*b < B.finiteContinuationAtArrival w c x u k := hmul.trans_le hwait
    have hgapneg : w*x k-B.finiteContinuationAtArrival w c x u k < 0 := by nlinarith
    have hlarge : e ≤ |w*x k-B.finiteContinuationAtArrival w c x u k| := by
      rw [abs_of_neg hgapneg]
      nlinarith [mul_pos hw hb]
    exact Or.inl (hlarge.trans (hLoss.symm.le.trans hSum))

end ProphetSecretary.Limiting
