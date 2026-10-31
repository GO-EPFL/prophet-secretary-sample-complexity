import ProphetSecretary.Limiting.HybridBellmanLoss
import ProphetSecretary.Limiting.HybridClockNullSets

/-!
# Measurability and integrability of actual hybrid Bellman loss

The true continuation is a bounded actual hybrid value on every physical
arrival. The complete reached-loss sum is bounded by a constant times the
finite retained-plus-Poisson count. This proves its integrability for every
measurable competing policy before any performance identity is invoked.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n N : ℕ} {Seed : Type*}

lemma FiniteIntensityHybridInstance.valueHybridThreshold_mul_eq
    (B : FiniteIntensityHybridInstance n) {w : ℝ} (hw : 0 < w) (c : ℝ)
    (A : Finset (Fin n)) (t : ℝ) (i : Option (Fin n)) :
    w*B.valueHybridThreshold w c () A t i =
      ((B.restrictIndividuals (i.elim A (fun j => A.erase j))).remainingHorizon (remainingTime t)).optimalScalarValue w (c*(remainingTime t : ℝ)) := by
  unfold FiniteIntensityHybridInstance.valueHybridThreshold FiniteIntensityHybridInstance.continuationValue
  rw [← mul_div_assoc,mul_div_cancel_left₀ _ hw.ne']

lemma FiniteIntensityHybridInstance.valueHybridThreshold_mul_bounds
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (A : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) (i : Option (Fin n)) :
    0 ≤ w*B.valueHybridThreshold w c () A t i ∧
      w*B.valueHybridThreshold w c () A t i ≤ 2*w*(B.cap : ℝ)+c := by
  rw [B.valueHybridThreshold_mul_eq hw c A t i]
  let C := (B.restrictIndividuals (i.elim A (fun j => A.erase j))).remainingHorizon (remainingTime t)
  have hd : 0 ≤ c*(remainingTime t : ℝ) := mul_nonneg hc (remainingTime t).property
  have hR : (remainingTime t : ℝ) ≤ 1 := by exact_mod_cast remainingTime_le_one ht
  have hD : c*(remainingTime t : ℝ) ≤ c := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hR hc
  have hV := C.optimalScalarValue_le hw.le hd
  have hM : C.expectedMaximum ≤ (B.cap : ℝ) := C.expectedMaximum_le_cap
  have hMH := mul_le_mul_of_nonneg_left hM hw.le
  refine ⟨C.optimalScalarValue_nonnegative hw.le hd,?_⟩
  have hPos : 0 ≤ w*(B.cap : ℝ) := mul_nonneg hw.le B.cap.property
  linarith

lemma FiniteIntensityHybridInstance.finiteContinuationAtArrival_bounds
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (x u : Fin (n+N) → ℝ) (k : Fin (n+N)) (ht : 0 ≤ u k) :
    0 ≤ B.finiteContinuationAtArrival w c x u k ∧
      B.finiteContinuationAtArrival w c x u k ≤ 2*w*(B.cap : ℝ)+c := by
  induction k using Fin.addCases with
  | left i =>
    simpa only [FiniteIntensityHybridInstance.finiteContinuationAtArrival,finiteHybridThreshold,Fin.addCases_left] using
      B.valueHybridThreshold_mul_bounds hw hc
        (retainedUnseen (Model.unseen (Model.history Finset.univ x u (u (i.castAdd N))))) ht (some i)
  | right j =>
    simpa only [FiniteIntensityHybridInstance.finiteContinuationAtArrival,finiteHybridThreshold,Fin.addCases_right] using
      B.valueHybridThreshold_mul_bounds hw hc
        (retainedUnseen (Model.unseen (Model.history Finset.univ x u (u (j.natAdd n))))) ht none

variable [MeasurableSpace Seed]

lemma HybridRule.measurable_reachedValueLoss (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Measurable (π.reachedValueLoss B w c) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := by fun_prop
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) := by fun_prop
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) := by fun_prop
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  have hXF (k : Fin (n+N)) : Measurable (fun v : Ω => combinedValues v.2.1 v.1 k) := measurable_combinedValues_family _ hx _ hv k
  have hUF (k : Fin (n+N)) : Measurable (fun v : Ω => combinedClocks v.2.2.1 v.1 k) := measurable_combinedClocks_family _ hu _ hv k
  have hV (k : Fin (n+N)) : Measurable (fun v : Ω => B.finiteContinuationAtArrival w c
      (combinedValues v.2.1 v.1) (combinedClocks v.2.2.1 v.1) k) :=
    B.measurable_finiteContinuationAtArrival hw.le hc hXF hUF k
  have hL (k : Fin (n+N)) : Measurable (fun v : Ω => π.arrivalValueLoss B w c (configurationMk N v.1,v.2) k) := by
    have hA := measurableSet_eq_fun ((π.asFinitePolicy N).measurable_action (π.asFinitePolicy_isMeasurable hπ N)
      hr hXF hUF Finset.univ k) (measurable_const (a := true))
    change Measurable (fun v : Ω => max (w*combinedValues v.2.1 v.1 k)
      (B.finiteContinuationAtArrival w c (combinedValues v.2.1 v.1) (combinedClocks v.2.2.1 v.1) k)-
      (if (π.asFinitePolicy N).action v.2.2.2 Finset.univ (combinedValues v.2.1 v.1) (combinedClocks v.2.2.1 v.1) k = true
        then w*combinedValues v.2.1 v.1 k else B.finiteContinuationAtArrival w c
          (combinedValues v.2.1 v.1) (combinedClocks v.2.2.1 v.1) k))
    exact ((hXF k).const_mul w |>.max (hV k)).sub (Measurable.ite hA ((hXF k).const_mul w) (hV k))
  change Measurable (fun v : Ω => ∑ k : Fin (n+N), if (π.asFinitePolicy N).Reaches v.2.2.2
    (combinedValues v.2.1 v.1) (combinedClocks v.2.2.1 v.1) k then
      π.arrivalValueLoss B w c (configurationMk N v.1,v.2) k else 0)
  apply Finset.measurable_fun_sum
  intro k _
  exact Measurable.ite ((π.asFinitePolicy N).measurableSet_reaches (π.asFinitePolicy_isMeasurable hπ N) hr hXF hUF k)
    (hL k) measurable_const

lemma HybridRule.integrable_reachedValueLoss (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) : Integrable (π.reachedValueLoss B w c) (B.law ν) := by
  have hCount : Integrable (fun v : HybridWorld n Seed => (v.1.1 : ℝ)) (B.law ν) :=
    (measurePreserving_fst (μ := configurationLaw B.intensity) (ν := B.individuals.worldLaw ν)).integrable_comp_of_integrable
      (configuration_count_integrable B.intensity)
  let K := 3*w*(B.cap : ℝ)+c
  have hDom : Integrable (fun v : HybridWorld n Seed => ((n : ℝ)+(v.1.1 : ℝ))*K) (B.law ν) :=
    ((integrable_const (n : ℝ)).add hCount).mul_const K
  apply hDom.mono' (π.measurable_reachedValueLoss hπ B hw hc).aestronglyMeasurable
  filter_upwards [realized_values_bounds B.individuals B.intensity ν B.individual_bounded B.intensity_supported,
    hybrid_combined_clocks_regular B.individuals B.intensity ν] with v hx ht
  rw [Real.norm_eq_abs,abs_of_nonneg (π.reachedValueLoss_nonnegative B w c v)]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hEach (k : Fin (n+v.1.1)) : π.arrivalValueLoss B w c v k ≤ K := by
    let x := combinedValues v.2.1 v.1.2
    let u := combinedClocks v.2.2.1 v.1.2
    let V := B.finiteContinuationAtArrival w c x u k
    have hV := B.finiteContinuationAtArrival_bounds hw hc x u k (ht.2 k).1.le
    have hX0 : 0 ≤ w*x k := mul_nonneg hw.le (hx k).1
    have hXH := mul_le_mul_of_nonneg_left (hx k).2 hw.le
    have hChoice : 0 ≤ if (π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ x u k = true then w*x k else V := by
      split_ifs
      · exact hX0
      · exact hV.1
    have hMax : max (w*x k) V ≤ w*x k+V := max_le (by linarith [hV.1]) (by linarith)
    change max (w*x k) V-(if _ then w*x k else V) ≤ K
    have hSub := sub_le_self (max (w*x k) V) hChoice
    dsimp only [K]
    linarith [hV.2]
  unfold HybridRule.reachedValueLoss
  calc
    _ ≤ ∑ _k : Fin (n+v.1.1), K := Finset.sum_le_sum fun k _ => by split_ifs; exact hEach k; exact hK
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add]

noncomputable def RandomizedHybridPolicy.expectedValueLoss (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) : ℝ := ∫ v, π.rule.reachedValueLoss B w c v ∂B.law π.seedLaw

lemma RandomizedHybridPolicy.expectedValueLoss_nonnegative (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) : 0 ≤ π.expectedValueLoss B w c :=
  integral_nonneg (π.rule.reachedValueLoss_nonnegative B w c)

lemma FiniteIntensityHybridInstance.valueThresholdPolicy_expectedValueLoss_zero (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) : (B.valueThresholdPolicy hw.le hc).expectedValueLoss B w c = 0 := by
  change (∫ v, (B.valueRule w c).reachedValueLoss B w c v ∂B.law (Measure.dirac ())) = 0
  simp only [B.valueRule_reachedValueLoss_zero hw c,integral_zero]

end ProphetSecretary.Limiting
