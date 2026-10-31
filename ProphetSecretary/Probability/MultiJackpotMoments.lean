import ProphetSecretary.Reach.RobustPathwise
import Mathlib.Probability.Independence.Integration

/-!
# Moments of independent dummy jackpot flags

The first moment of the number of flags is `Np`; the ordered pair count has expectation
at most `N²p²`. These are explicit finite estimates, used before taking `p` to zero.
-/

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped BigOperators Classical

namespace ProphetSecretary.Model.MultiJackpot

variable {N : ℕ}

lemma measurable_bit (j : Fin N) : Measurable (fun b : Fin N → Bool => bit b j) := by
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply j) measurable_const) measurable_const measurable_const

lemma integrable_bit (p : unitInterval) (j : Fin N) :
    Integrable (fun b : Fin N → Bool => bit b j) (ProphetSecretary.Probability.jackpotCoins N p) := by
  apply Integrable.of_bound (measurable_bit j).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun b => by rw [Real.norm_eq_abs, abs_of_nonneg (bit_nonnegative b j)]; exact bit_le_one b j

lemma integral_bit (p : unitInterval) (j : Fin N) :
    (∫ b : Fin N → Bool, bit b j ∂ProphetSecretary.Probability.jackpotCoins N p) = (p : ℝ) := by
  have h := integral_indicator_const (μ := ProphetSecretary.Probability.jackpotCoins N p) (s := {b : Fin N → Bool | b j = true}) (1 : ℝ)
    (measurableSet_eq_fun (measurable_pi_apply j) measurable_const)
  simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, smul_eq_mul, mul_one, bit,
    ProphetSecretary.Probability.jackpotCoins_coordinate_probability] using h

lemma integral_bitCount (p : unitInterval) :
    (∫ b : Fin N → Bool, bitCount b ∂ProphetSecretary.Probability.jackpotCoins N p) = N * (p : ℝ) := by
  unfold bitCount
  rw [integral_finsetSum _ (fun j _ => integrable_bit p j)]
  simp only [integral_bit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma integrable_bit_product (p : unitInterval) (j l : Fin N) :
    Integrable (fun b : Fin N → Bool => bit b j * bit b l) (ProphetSecretary.Probability.jackpotCoins N p) := by
  apply Integrable.of_bound ((measurable_bit j).mul (measurable_bit l)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun b => by
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (bit_nonnegative b j) (bit_nonnegative b l))]
    exact mul_le_one₀ (bit_le_one b j) (bit_nonnegative b l) (bit_le_one b l)

lemma integral_bit_product (p : unitInterval) {j l : Fin N} (hjl : j ≠ l) :
    (∫ b : Fin N → Bool, bit b j * bit b l ∂ProphetSecretary.Probability.jackpotCoins N p) = (p : ℝ) ^ 2 := by
  have hInd := (iIndepFun_pi (μ := fun _ : Fin N => bernoulliMeasure true false p)
    (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hjl
  have h := hInd.comp (measurable_of_finite (fun b : Bool => if b = true then (1 : ℝ) else 0))
    (measurable_of_finite (fun b : Bool => if b = true then (1 : ℝ) else 0))
  have he := h.integral_fun_mul_eq_mul_integral (measurable_bit j).aestronglyMeasurable
    (measurable_bit l).aestronglyMeasurable
  change (∫ b : Fin N → Bool, bit b j * bit b l ∂ProphetSecretary.Probability.jackpotCoins N p) =
    (∫ b : Fin N → Bool, bit b j ∂ProphetSecretary.Probability.jackpotCoins N p) *
      (∫ b : Fin N → Bool, bit b l ∂ProphetSecretary.Probability.jackpotCoins N p) at he
  rw [integral_bit, integral_bit] at he
  simpa only [pow_two] using he

lemma integrable_pairCount (p : unitInterval) :
    Integrable (@pairCount N) (ProphetSecretary.Probability.jackpotCoins N p) := by
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro l _
  by_cases hjl : j = l
  · simp [hjl]
  · simpa only [if_pos hjl] using integrable_bit_product p j l

lemma integral_pairCount_le (p : unitInterval) :
    (∫ b : Fin N → Bool, pairCount b ∂ProphetSecretary.Probability.jackpotCoins N p) ≤ (N : ℝ) ^ 2 * (p : ℝ) ^ 2 := by
  unfold pairCount
  rw [integral_finsetSum]
  · calc
      _ ≤ ∑ _j : Fin N, ∑ _l : Fin N, (p : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [integral_finsetSum]
        · apply Finset.sum_le_sum
          intro l _
          by_cases hjl : j = l
          · simp only [hjl, ne_eq, not_true_eq_false, if_false, integral_zero]
            exact sq_nonneg _
          · simp only [if_pos hjl]
            exact le_of_eq (integral_bit_product p hjl)
        · intro l _
          by_cases hjl : j = l
          · simp [hjl]
          · simpa only [if_pos hjl] using integrable_bit_product p j l
      _ = (N : ℝ) ^ 2 * (p : ℝ) ^ 2 := by simp [pow_two, mul_assoc]
  · intro j _
    apply integrable_finsetSum
    intro l _
    by_cases hjl : j = l
    · simp [hjl]
    · simpa only [if_pos hjl] using integrable_bit_product p j l

lemma measurable_bitCount : Measurable (@bitCount N) :=
  Finset.measurable_sum _ (fun j _ => measurable_bit j)

lemma measurable_pairCount : Measurable (@pairCount N) := by
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro l _
  by_cases hjl : j = l
  · simpa only [hjl, ne_eq, not_true_eq_false, if_false] using (measurable_const : Measurable (fun _ : Fin N → Bool => (0 : ℝ)))
  · simp only [if_pos hjl]
    exact (measurable_bit j).mul (measurable_bit l)

private lemma integral_comp_measurable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {f : Ω → Ω'} (hf : MeasurePreserving f μ ν)
    {g : Ω' → ℝ} (hg : Measurable g) : (∫ ω, g (f ω) ∂μ) = ∫ ω, g ω ∂ν := by
  have h := integral_map (μ := μ) hf.measurable.aemeasurable hg.aestronglyMeasurable
  rw [hf.map_eq] at h
  exact h.symm

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma coupled_integral_bitCount (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    (∫ z : CouplingWorld n N Seed, bitCount z.1 ∂couplingLaw P N p ν) = N * (p : ℝ) := by
  unfold couplingLaw
  rw [integral_comp_measurable (measurePreserving_fst : MeasurePreserving Prod.fst
    (couplingLaw P N p ν) (ProphetSecretary.Probability.jackpotCoins N p)) measurable_bitCount]
  exact integral_bitCount p

lemma coupled_integral_pairCount_le (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    (∫ z : CouplingWorld n N Seed, pairCount z.1 ∂couplingLaw P N p ν) ≤ (N : ℝ) ^ 2 * (p : ℝ) ^ 2 := by
  unfold couplingLaw
  rw [integral_comp_measurable (measurePreserving_fst : MeasurePreserving Prod.fst
    (couplingLaw P N p ν) (ProphetSecretary.Probability.jackpotCoins N p)) measurable_pairCount]
  exact integral_pairCount_le p

lemma coupled_integral_any_le (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    (∫ z : CouplingWorld n N Seed, (if ∃ j, z.1 j = true then (1 : ℝ) else 0) ∂couplingLaw P N p ν) ≤ N * (p : ℝ) := by
  have hmeas : Measurable (fun b : Fin N → Bool => if ∃ j, b j = true then (1 : ℝ) else 0) :=
    Measurable.ite (ProphetSecretary.Probability.measurableSet_badJackpotCoins N) measurable_const measurable_const
  unfold couplingLaw
  rw [integral_comp_measurable (measurePreserving_fst : MeasurePreserving Prod.fst
    (couplingLaw P N p ν) (ProphetSecretary.Probability.jackpotCoins N p)) hmeas]
  have h := integral_indicator_const (μ := ProphetSecretary.Probability.jackpotCoins N p) (1 : ℝ)
    (ProphetSecretary.Probability.measurableSet_badJackpotCoins N)
  have he : (∫ b : Fin N → Bool, (if ∃ j, b j = true then (1 : ℝ) else 0) ∂ProphetSecretary.Probability.jackpotCoins N p) =
      (ProphetSecretary.Probability.jackpotCoins N p).real {b | ProphetSecretary.Probability.badJackpotCoins b} := by
    simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, smul_eq_mul, mul_one, ProphetSecretary.Probability.badJackpotCoins] using h
  rw [he]
  exact ProphetSecretary.Probability.badJackpotCoins_probability_le N p

lemma coupled_integral_reachScore (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (π : Policy Seed (n + N)) (hπ : π.IsMeasurable) :
    (∫ z : CouplingWorld n N Seed, reachScore π z.2.2.2 z.2.1 z.2.2.1 z.1 ∂couplingLaw P N p ν) =
      (p : ℝ) * ∑ j : Fin N, π.reachProbability (P.appendZeros N) ν (Fin.natAdd n j) := by
  let μrest := P.valuesLaw.prod ((Instance.clocksLaw (n + N)).prod ν)
  let R := (Fin n → ℝ) × ((Fin (n + N) → ℝ) × Seed)
  let T : R → World (n + N) Seed := fun z => (ZeroSimulation.appendValues z.1, z.2)
  have hT : MeasurePreserving T μrest ((P.appendZeros N).worldLaw ν) :=
    (P.appendValues_measurePreserving N).prod (MeasurePreserving.id ((Instance.clocksLaw (n + N)).prod ν))
  let E (j : Fin N) : Set (World (n + N) Seed) :=
    {ω | π.Reaches ω.2.2 ω.1 ω.2.1 (Fin.natAdd n j)}
  have hE (j : Fin N) : MeasurableSet (E j) := π.measurableSet_reaches hπ
    (measurable_snd.comp measurable_snd)
    (fun a => (measurable_pi_apply a).comp measurable_fst)
    (fun a => (measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)) _
  let F (j : Fin N) : R → ℝ := fun z => if T z ∈ E j then 1 else 0
  have hF (j : Fin N) : Measurable (F j) := Measurable.ite (hT.measurable (hE j)) measurable_const measurable_const
  have hterm (j : Fin N) :
      (∫ z : CouplingWorld n N Seed,
        (if z.1 j = true ∧ π.Reaches z.2.2.2 (ZeroSimulation.appendValues z.2.1) z.2.2.1 (Fin.natAdd n j)
          then (1 : ℝ) else 0) ∂couplingLaw P N p ν) =
          (p : ℝ) * π.reachProbability (P.appendZeros N) ν (Fin.natAdd n j) := by
    have hprod := indepFun_prod (μ := ProphetSecretary.Probability.jackpotCoins N p) (ν := μrest) (measurable_bit j) (hF j)
    have hi := hprod.integral_fun_mul_eq_mul_integral
      ((measurable_bit j).comp measurable_fst).aestronglyMeasurable ((hF j).comp measurable_snd).aestronglyMeasurable
    have hbit : (∫ z : CouplingWorld n N Seed, bit z.1 j ∂couplingLaw P N p ν) = (p : ℝ) := by
      unfold couplingLaw
      rw [integral_comp_measurable (measurePreserving_fst : MeasurePreserving Prod.fst
        (couplingLaw P N p ν) (ProphetSecretary.Probability.jackpotCoins N p)) (measurable_bit j)]
      exact integral_bit p j
    have hreach : (∫ z : CouplingWorld n N Seed, F j z.2 ∂couplingLaw P N p ν) =
        π.reachProbability (P.appendZeros N) ν (Fin.natAdd n j) := by
      unfold couplingLaw
      rw [integral_comp_measurable (measurePreserving_snd : MeasurePreserving Prod.snd
        (couplingLaw P N p ν) μrest) (hF j)]
      let G : World (n + N) Seed → ℝ := fun ω => if ω ∈ E j then 1 else 0
      have hG : Measurable G := Measurable.ite (hE j) measurable_const measurable_const
      have hiF := integral_comp_measurable hT hG
      change (∫ z : R, G (T z) ∂μrest) = _
      rw [hiF]
      have hiG := integral_indicator_const (μ := (P.appendZeros N).worldLaw ν) (1 : ℝ) (hE j)
      simpa only [G, Set.indicator, Pi.one_apply, smul_eq_mul, mul_one, Policy.reachProbability, E] using hiG
    change (∫ z : CouplingWorld n N Seed, bit z.1 j * F j z.2 ∂couplingLaw P N p ν) =
      (∫ z : CouplingWorld n N Seed, bit z.1 j ∂couplingLaw P N p ν) *
        (∫ z : CouplingWorld n N Seed, F j z.2 ∂couplingLaw P N p ν) at hi
    rw [hbit, hreach] at hi
    convert hi using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      dsimp [bit, F, T, E]
      split_ifs <;> simp_all
  unfold reachScore
  rw [integral_finsetSum]
  · simp_rw [hterm]
    rw [Finset.mul_sum]
  · intro j _
    apply Integrable.of_bound (Measurable.ite
      (((measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_fst) measurable_const)).inter
        ((zeroWorld_measurePreserving P N p ν).measurable (hE j))) measurable_const measurable_const).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun z => by split_ifs <;> norm_num

lemma coupled_integrable_bitCount (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    Integrable (fun z : CouplingWorld n N Seed => bitCount z.1) (couplingLaw P N p ν) := by
  have hp : MeasurePreserving (fun z : CouplingWorld n N Seed => z.1)
      (couplingLaw P N p ν) (ProphetSecretary.Probability.jackpotCoins N p) := measurePreserving_fst
  exact hp.integrable_comp_of_integrable (integrable_finsetSum _ (fun j _ => integrable_bit p j))

lemma coupled_integrable_pairCount (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    Integrable (fun z : CouplingWorld n N Seed => pairCount z.1) (couplingLaw P N p ν) := by
  have hp : MeasurePreserving (fun z : CouplingWorld n N Seed => z.1)
      (couplingLaw P N p ν) (ProphetSecretary.Probability.jackpotCoins N p) := measurePreserving_fst
  exact hp.integrable_comp_of_integrable (integrable_pairCount p)

lemma coupled_integrable_any (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    Integrable (fun z : CouplingWorld n N Seed => if ∃ j, z.1 j = true then (1 : ℝ) else 0)
      (couplingLaw P N p ν) := by
  have hmeas : Measurable (fun z : CouplingWorld n N Seed => if ∃ j, z.1 j = true then (1 : ℝ) else 0) :=
    Measurable.ite (measurable_fst (ProphetSecretary.Probability.measurableSet_badJackpotCoins N)) measurable_const measurable_const
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun z => by split_ifs <;> norm_num

lemma coupled_integrable_reachScore (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (π : Policy Seed (n + N)) (hπ : π.IsMeasurable) :
    Integrable (fun z : CouplingWorld n N Seed => reachScore π z.2.2.2 z.2.1 z.2.2.1 z.1)
      (couplingLaw P N p ν) := by
  unfold reachScore
  apply integrable_finsetSum
  intro j _
  have hE : MeasurableSet {ω : World (n + N) Seed | π.Reaches ω.2.2 ω.1 ω.2.1 (Fin.natAdd n j)} :=
    π.measurableSet_reaches hπ (measurable_snd.comp measurable_snd)
      (fun a => (measurable_pi_apply a).comp measurable_fst)
      (fun a => (measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)) _
  have hcond : MeasurableSet {z : CouplingWorld n N Seed |
      z.1 j = true ∧ π.Reaches z.2.2.2 (ZeroSimulation.appendValues z.2.1) z.2.2.1 (Fin.natAdd n j)} :=
    (measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_fst) measurable_const).inter
      ((zeroWorld_measurePreserving P N p ν).measurable hE)
  apply Integrable.of_bound (Measurable.ite hcond measurable_const measurable_const).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun z => by split_ifs <;> norm_num

end ProphetSecretary.Model.MultiJackpot
