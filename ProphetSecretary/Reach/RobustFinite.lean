import ProphetSecretary.Probability.MultiJackpotMoments
import ProphetSecretary.Reach.Zeros

/-!
# Uniform finite multi-jackpot estimates

These estimates precede the ordered limits in `lem:robust`. They hold for every
measurable history-dependent policy, with no optimality or Markov restriction.
-/

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped BigOperators

namespace ProphetSecretary.Model.MultiJackpot

variable {n : ℕ}

lemma appendJackpots_expectedMaximum_lower (P : Instance n) (N : ℕ) (p : unitInterval)
    {H A : ℝ} (hH : 0 ≤ H) (hA : 0 ≤ A) (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H) :
    P.expectedMaximum + A * N * (p : ℝ) - H * N * (p : ℝ) - A * (N : ℝ) ^ 2 * (p : ℝ) ^ 2 ≤
      (P.appendJackpots N p A hA).expectedMaximum := by
  let C := couplingLaw P N p (Measure.dirac ())
  have hp := jackpotWorld_measurePreserving P N p (Measure.dirac ()) A hA
  have hpv : MeasurePreserving (fun z : CouplingWorld n N Unit => (jackpotWorld A z).1) C
      (P.appendJackpots N p A hA).valuesLaw := measurePreserving_fst.comp hp
  have hx : MeasurePreserving (fun z : CouplingWorld n N Unit => z.2.1) C P.valuesLaw :=
    measurePreserving_fst.comp measurePreserving_snd
  have hP := P.integrable_maximum_of_bounded hbound
  have hJ := P.appendJackpots_integrable_maximum N p hA hH hbound
  have hiM : Integrable (fun z : CouplingWorld n N Unit => Instance.maximum z.2.1) C :=
    hx.integrable_comp_of_integrable hP
  have hiC := coupled_integrable_bitCount P N p (Measure.dirac ())
  have hiB := coupled_integrable_any P N p (Measure.dirac ())
  have hiPairs := coupled_integrable_pairCount P N p (Measure.dirac ())
  have hi₀ : Integrable (fun z : CouplingWorld n N Unit => Instance.maximum z.2.1 + A * bitCount z.1) C :=
    hiM.add (hiC.const_mul A)
  have hi₁ : Integrable (fun z : CouplingWorld n N Unit =>
      Instance.maximum z.2.1 + A * bitCount z.1 - H * (if ∃ j, z.1 j = true then (1 : ℝ) else 0)) C :=
    hi₀.sub (hiB.const_mul H)
  have hi₂ : Integrable (fun z : CouplingWorld n N Unit =>
      (Instance.maximum z.2.1 + A * bitCount z.1 - H * (if ∃ j, z.1 j = true then (1 : ℝ) else 0)) - A * pairCount z.1) C :=
    hi₁.sub (hiPairs.const_mul A)
  have hsupp : ∀ᵐ z : CouplingWorld n N Unit ∂C, ∀ j, z.2.1 j ≤ H := by
    have hxb : ∀ᵐ x ∂P.valuesLaw, ∀ j, x j ≤ H := by
      rw [ae_all_iff]
      intro j
      exact (measurePreserving_eval P.law j).quasiMeasurePreserving.ae (hbound j)
    exact hx.quasiMeasurePreserving.ae hxb

  have hmain := integral_mono_ae hi₂ (hpv.integrable_comp_of_integrable hJ) (by
    filter_upwards [hsupp] with z hz
    exact maximum_jackpotValues_lower A H hA hH z.1 z.2.1 hz)
  have hbase := integral_map (μ := C) hx.measurable.aemeasurable Instance.measurable_maximum.aestronglyMeasurable
  rw [hx.map_eq] at hbase
  have hjack := integral_map (μ := C) hpv.measurable.aemeasurable Instance.measurable_maximum.aestronglyMeasurable
  rw [hpv.map_eq] at hjack
  change (∫ z : CouplingWorld n N Unit,
      (Instance.maximum z.2.1 + A * bitCount z.1 - H * (if ∃ j, z.1 j = true then (1 : ℝ) else 0)) - A * pairCount z.1 ∂C) ≤
      ∫ z : CouplingWorld n N Unit, Instance.maximum (jackpotWorld A z).1 ∂C at hmain
  rw [integral_sub hi₁ (hiPairs.const_mul A), integral_sub hi₀ (hiB.const_mul H),
    integral_add hiM (hiC.const_mul A)] at hmain
  simp only [integral_const_mul] at hmain
  rw [← hbase, ← hjack, coupled_integral_bitCount] at hmain
  have hbad := mul_le_mul_of_nonneg_left (coupled_integral_any_le P N p (Measure.dirac ())) hH
  have hpairs := mul_le_mul_of_nonneg_left (coupled_integral_pairCount_le P N p (Measure.dirac ())) hA
  change P.expectedMaximum + A * (N * (p : ℝ)) - H * (∫ z : CouplingWorld n N Unit,
      (if ∃ j, z.1 j = true then (1 : ℝ) else 0) ∂C) - A * (∫ z : CouplingWorld n N Unit, pairCount z.1 ∂C) ≤
      (P.appendJackpots N p A hA).expectedMaximum at hmain
  nlinarith

lemma appendJackpots_expectedReward_upper (P : Instance n) (N : ℕ) (p : unitInterval)
    (π : RandomizedPolicy (n + N)) {H A : ℝ} (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H) :
    π.expectedReward (P.appendJackpots N p A hA) ≤
      π.expectedReward (P.appendZeros N) + H * N * (p : ℝ) +
        A * (p : ℝ) * (∑ j : Fin N, π.rule.reachProbability (P.appendZeros N) π.seedLaw (Fin.natAdd n j)) +
          A * (N : ℝ) ^ 2 * (p : ℝ) ^ 2 := by
  let C := couplingLaw P N p π.seedLaw
  have hp := jackpotWorld_measurePreserving P N p π.seedLaw A hA
  have hz := zeroWorld_measurePreserving P N p π.seedLaw
  have hx : MeasurePreserving (fun z : CouplingWorld n N π.Seed => z.2.1) C P.valuesLaw :=
    measurePreserving_fst.comp measurePreserving_snd
  have hP := P.integrable_maximum_of_bounded hbound
  have hiR : Integrable (fun z : CouplingWorld n N π.Seed => π.realizedReward (zeroWorld z)) C := hz.integrable_comp_of_integrable
    (π.integrable_realizedReward (P.appendZeros N) (P.appendZeros_integrable_maximum N hP))
  have hiB := coupled_integrable_any P N p π.seedLaw
  have hiScore := coupled_integrable_reachScore P N p π.seedLaw π.rule π.measurable_rule
  have hiPairs := coupled_integrable_pairCount P N p π.seedLaw
  have hi₀ : Integrable (fun z : CouplingWorld n N π.Seed => π.realizedReward (zeroWorld z) +
      H * (if ∃ j, z.1 j = true then (1 : ℝ) else 0)) C := hiR.add (hiB.const_mul H)
  have hi₁ : Integrable (fun z : CouplingWorld n N π.Seed => (π.realizedReward (zeroWorld z) +
      H * (if ∃ j, z.1 j = true then (1 : ℝ) else 0)) + A * reachScore π.rule z.2.2.2 z.2.1 z.2.2.1 z.1) C :=
    hi₀.add (hiScore.const_mul A)
  have hi₂ : Integrable (fun z : CouplingWorld n N π.Seed => ((π.realizedReward (zeroWorld z) +
      H * (if ∃ j, z.1 j = true then (1 : ℝ) else 0)) + A * reachScore π.rule z.2.2.2 z.2.1 z.2.2.1 z.1) + A * pairCount z.1) C :=
    hi₁.add (hiPairs.const_mul A)
  have hsupp : ∀ᵐ z : CouplingWorld n N π.Seed ∂C, (∀ j, 0 ≤ z.2.1 j) ∧ (∀ j, z.2.1 j ≤ H) := by
    have hb : ∀ᵐ x ∂P.valuesLaw, ∀ j, x j ≤ H := by
      rw [ae_all_iff]
      intro j
      exact (measurePreserving_eval P.law j).quasiMeasurePreserving.ae (hbound j)
    have hall : ∀ᵐ x ∂P.valuesLaw, (∀ j, 0 ≤ x j) ∧ (∀ j, x j ≤ H) := by
      filter_upwards [P.ae_nonnegative, hb] with x hx0 hxb
      exact ⟨hx0, hxb⟩
    exact hx.quasiMeasurePreserving.ae hall
  have hclocks : ∀ᵐ z : CouplingWorld n N π.Seed ∂C, ∀ j, z.2.2.1 j ≤ 1 := by
    filter_upwards [hz.quasiMeasurePreserving.ae ((P.appendZeros N).world_clocks_mem_unitInterval π.seedLaw)] with z hz
    exact fun j => (hz j).2
  have hmain := integral_mono_ae
    (hp.integrable_comp_of_integrable (π.integrable_realizedReward _ (P.appendJackpots_integrable_maximum N p hA hH hbound))) hi₂ (by
      filter_upwards [hsupp, hclocks] with z hz hu
      exact reward_jackpotValues_upper π.rule z.2.2.2 A H hA hH z.1 z.2.1 hz.1 hz.2 z.2.2.1 hu)
  have hzero := integral_map (μ := C) hz.measurable.aemeasurable π.measurable_realizedReward.aestronglyMeasurable
  rw [hz.map_eq] at hzero
  have hjack := integral_map (μ := C) hp.measurable.aemeasurable π.measurable_realizedReward.aestronglyMeasurable
  rw [hp.map_eq] at hjack
  change (∫ z : CouplingWorld n N π.Seed, π.realizedReward (jackpotWorld A z) ∂C) ≤
    ∫ z : CouplingWorld n N π.Seed, ((π.realizedReward (zeroWorld z) +
      H * (if ∃ j, z.1 j = true then (1 : ℝ) else 0)) + A * reachScore π.rule z.2.2.2 z.2.1 z.2.2.1 z.1) + A * pairCount z.1 ∂C at hmain
  rw [integral_add hi₁ (hiPairs.const_mul A), integral_add hi₀ (hiScore.const_mul A),
    integral_add hiR (hiB.const_mul H)] at hmain
  simp only [integral_const_mul] at hmain
  rw [← hzero, ← hjack, coupled_integral_reachScore P N p π.seedLaw π.rule π.measurable_rule] at hmain
  have hbad := mul_le_mul_of_nonneg_left (coupled_integral_any_le P N p π.seedLaw) hH
  have hpairs := mul_le_mul_of_nonneg_left (coupled_integral_pairCount_le P N p π.seedLaw) hA
  change π.expectedReward (P.appendJackpots N p A hA) ≤ π.expectedReward (P.appendZeros N) +
    H * (∫ z : CouplingWorld n N π.Seed, (if ∃ j, z.1 j = true then (1 : ℝ) else 0) ∂C) +
      A * ((p : ℝ) * ∑ j : Fin N, π.rule.reachProbability (P.appendZeros N) π.seedLaw (Fin.natAdd n j)) +
        A * (∫ z : CouplingWorld n N π.Seed, pairCount z.1 ∂C) at hmain
  nlinarith

/-- The zero-offer duration comparison and its causal simulation convert the finite
reach term to the base scalar optimum. The error is uniform over the competing policy. -/
lemma appendJackpots_expectedReward_le_scalar (P : Instance n) (N : ℕ) (hN : 0 < N)
    (p : unitInterval) (π : RandomizedPolicy (n + N)) {H A : ℝ}
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H) :
    π.expectedReward (P.appendJackpots N p A hA) ≤
      optimalScalarValue P 1 (A * N * (p : ℝ)) + 20 * (A * N * (p : ℝ)) / Real.sqrt (N : ℝ) +
        H * N * (p : ℝ) + A * (N : ℝ) ^ 2 * (p : ℝ) ^ 2 := by
  let d : ℝ := A * N * (p : ℝ)
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg hA (Nat.cast_nonneg N)) p.2.1
  have hP := P.integrable_maximum_of_bounded hbound
  have hq := π.rule.meanDuration_ge_average_zeroReach_sub_discrepancy π.measurable_rule hN (P.appendZeros N) π.seedLaw
  rw [(P.appendZeros N).mean_zeroClockDiscrepancy_eq π.seedLaw] at hq
  have hdis := ProphetSecretary.Reach.ZeroReach.expected_uniform_discrepancy_le N hN
  have hq' : (∑ j : Fin N, π.rule.reachProbability (P.appendZeros N) π.seedLaw (Fin.natAdd n j)) / N ≤
      π.expectedDuration (P.appendZeros N) + 20 / Real.sqrt (N : ℝ) := by
    change (∑ j : Fin N, π.rule.reachProbability (P.appendZeros N) π.seedLaw (Fin.natAdd n j)) / N -
      (∫ z : Fin N → ℝ, ProphetSecretary.Reach.ZeroReach.discrepancy z ∂Instance.clocksLaw N) ≤
        π.expectedDuration (P.appendZeros N) at hq
    linarith
  have hcoef := mul_le_mul_of_nonneg_left hq' hd
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have he : d * ((∑ j : Fin N, π.rule.reachProbability (P.appendZeros N) π.seedLaw (Fin.natAdd n j)) / N) =
      A * (p : ℝ) * (∑ j : Fin N, π.rule.reachProbability (P.appendZeros N) π.seedLaw (Fin.natAdd n j)) := by
    dsimp [d]
    field_simp [hNr]
  rw [he] at hcoef
  have hs₁ := π.scalarObjective_le_simulateZeros P hP (w := 1) (c := d) hd
  have hs₂ := scalarObjective_le_optimal π.simulateZeros P hP zero_le_one hd
  have hs : π.expectedReward (P.appendZeros N) + d * π.expectedDuration (P.appendZeros N) ≤
      optimalScalarValue P 1 d := by
    have h := hs₁.trans hs₂
    rw [π.scalarObjective_eq (P.appendZeros N) (P.appendZeros_integrable_maximum N hP)] at h
    simpa only [one_mul] using h
  have hraw := appendJackpots_expectedReward_upper P N p π hH hA hbound
  have herr : d * (20 / Real.sqrt (N : ℝ)) = 20 * d / Real.sqrt (N : ℝ) := by ring
  change π.expectedReward (P.appendJackpots N p A hA) ≤
      optimalScalarValue P 1 d + 20 * d / Real.sqrt (N : ℝ) + H * N * (p : ℝ) + A * (N : ℝ) ^ 2 * (p : ℝ) ^ 2
  rw [mul_add, herr] at hcoef
  nlinarith

/-- Taking the supremum over all policies does not require an optimal policy to exist. -/
lemma appendJackpots_optimalReward_le_scalar (P : Instance n) (N : ℕ) (hN : 0 < N)
    (p : unitInterval) {H A : ℝ} (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H) :
    optimalScalarValue (P.appendJackpots N p A hA) 1 0 ≤
      optimalScalarValue P 1 (A * N * (p : ℝ)) + 20 * (A * N * (p : ℝ)) / Real.sqrt (N : ℝ) +
        H * N * (p : ℝ) + A * (N : ℝ) ^ 2 * (p : ℝ) ^ 2 := by
  apply csSup_le (scalarValues_nonempty (P.appendJackpots N p A hA) 1 0)
  rintro v ⟨π, rfl⟩
  rw [π.scalarObjective_eq _ (P.appendJackpots_integrable_maximum N p hA hH hbound)]
  simp only [one_mul, zero_mul, add_zero]
  exact appendJackpots_expectedReward_le_scalar P N hN p π hH hA hbound

end ProphetSecretary.Model.MultiJackpot
