import ProphetSecretary.Limiting.HybridBellmanIdentityZeroIntensity
import ProphetSecretary.Model.BellmanLossProbability

/-!
# Actual hybrid regret controls reached-loss events

The scalar regret is the integral of the nonnegative reached Bellman-loss sum.
Markov's inequality therefore bounds the probability of a large reached loss,
including the zero-intensity and zero-benchmark auxiliary instances.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*}

lemma HybridRule.arrivalValueLoss_le_reachedValueLoss (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) (v : HybridWorld n Seed)
    (k : Fin (n+v.1.1))
    (hr : (π.asFinitePolicy v.1.1).Reaches v.2.2.2
      (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k) :
    π.arrivalValueLoss B w c v k ≤ π.reachedValueLoss B w c v := by
  calc
    _ = if (π.asFinitePolicy v.1.1).Reaches v.2.2.2
        (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k then
          π.arrivalValueLoss B w c v k else 0 := (if_pos hr).symm
    _ ≤ ∑ j : Fin (n+v.1.1), if (π.asFinitePolicy v.1.1).Reaches v.2.2.2
        (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) j then
          π.arrivalValueLoss B w c v j else 0 :=
      Finset.single_le_sum (f := fun j : Fin (n+v.1.1) =>
        if (π.asFinitePolicy v.1.1).Reaches v.2.2.2 (combinedValues v.2.1 v.1.2)
          (combinedClocks v.2.2.1 v.1.2) j then π.arrivalValueLoss B w c v j else 0)
        (fun j _ => by split_ifs; exact π.arrivalValueLoss_nonnegative B w c v j; exact le_rfl)
        (Finset.mem_univ k)

lemma RandomizedHybridPolicy.measurableSet_valueLossLevel (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (e : ℝ) :
    MeasurableSet {v | e ≤ π.rule.reachedValueLoss B w c v} :=
  measurableSet_le measurable_const (π.rule.measurable_reachedValueLoss π.measurable_rule B hw hc)

theorem RandomizedHybridPolicy.valueLossLevel_probability_le_regret (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {w c e : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (he : 0 < e) :
    (B.law π.seedLaw).real {v | e ≤ π.rule.reachedValueLoss B w c v} ≤
      (B.optimalScalarValue w c-π.scalarObjective B w c)/e := by
  have hi := π.rule.integrable_reachedValueLoss π.measurable_rule B π.seedLaw hw hc
  have hn : 0 ≤ᵐ[B.law π.seedLaw] π.rule.reachedValueLoss B w c :=
    Eventually.of_forall (π.rule.reachedValueLoss_nonnegative B w c)
  have h := mul_meas_ge_le_integral_of_nonneg hn hi e
  change e*(B.law π.seedLaw).real {v | e ≤ π.rule.reachedValueLoss B w c v} ≤
    π.expectedValueLoss B w c at h
  rw [← π.actual_bellmanIdentity B ha hw hc] at h
  exact (le_div_iff₀ he).mpr (by simpa only [mul_comm] using h)

end ProphetSecretary.Limiting
