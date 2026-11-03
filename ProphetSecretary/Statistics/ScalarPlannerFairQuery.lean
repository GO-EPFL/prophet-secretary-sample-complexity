import ProphetSecretary.Analysis.MultilevelSeedMap
import ProphetSecretary.Statistics.PlannerFairSeed
import ProphetSecretary.Statistics.ScalarPlannerRoundedAccuracy

/-!
# Scalar estimates from finite fair bits

Decoding all seeds independently gives the same law on recursive trees as
rounding the ideal seeds at every level. The evaluator reads only the decoded
grid seeds. Its hard bit budget includes the full reservoirs, whether or not
all branches of a particular tree are visited.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ} {k : Fin n → ℕ}

lemma scalarPlannerRoundedQuery_eq_map (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) (r : ℕ) (p : ℝ)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (seed : Fin (confidenceCopyCount p H) → MultilevelTree (PlannerUniformSeed n) r) :
    (scalarPlannerRoundedQuery y N hN x r p H seed).value =
      (scalarPlannerQueryAtLevel y x r p H
        (fun j => multilevelTreeMap (plannerRoundSeed N hN) r (seed j))).value := by
  have hD : scalarPlannerRoundedRecursion y N hN =
      (scalarPlannerRecursion y).mapSeed (plannerRoundSeed N hN) := rfl
  have hE (t : MultilevelTree (PlannerUniformSeed n) r) :
      (scalarPlannerRoundedSingle y N hN x r t).1 =
        (scalarPlannerSingle y x r (multilevelTreeMap (plannerRoundSeed N hN) r t)).1 := by
    simp only [scalarPlannerRoundedSingle, scalarPlannerSingle, hD, multilevelEstimate_mapSeed]
  by_cases he : (scalarPlannerRecursion y).isEmpty x = true
  · simp only [scalarPlannerRoundedQuery, scalarPlannerQueryAtLevel, he, if_true]
  · simp only [scalarPlannerRoundedQuery, scalarPlannerQueryAtLevel, if_neg he,
      confidenceMedianCopies_value, hE]

/-- Evaluate the scalar query after decoding each supplied finite-bit seed. -/
noncomputable def scalarPlannerFairQuery (y : (i : Fin n) → Fin (k i) → ℝ)
    (b : ℕ) (x : ScalarPlannerState n) (r : ℕ) (p : ℝ) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (bits : Fin (confidenceCopyCount p H) → MultilevelTree (PlannerFairSeed n b) r) : MedianCopiesResult ℝ :=
  scalarPlannerQueryAtLevel y x r p H (fun j => multilevelTreeMap (plannerFairSeedReal b) r (bits j))

/-- The count of bit reads for decoding a full collection of copy trees. -/
def scalarPlannerFairReads {m : ℕ} (b r : ℕ)
    (bits : Fin m → MultilevelTree (PlannerFairSeed n b) r) : ℕ :=
  ∑ j : Fin m, multilevelTreeSeedCount r (bits j) * ((3*n+2)*b)

lemma scalarPlannerFairReads_le {m : ℕ} (b r : ℕ)
    (bits : Fin m → MultilevelTree (PlannerFairSeed n b) r) :
    scalarPlannerFairReads b r bits ≤ m * (4*16^r) * ((3*n+2)*b) := by
  unfold scalarPlannerFairReads
  calc
    _ ≤ ∑ _j : Fin m, (4*16^r)*((3*n+2)*b) := Finset.sum_le_sum (fun j _ =>
      Nat.mul_le_mul_right _ (multilevelTreeSeedCount_le r (bits j)))
    _ = _ := by simp [Nat.mul_assoc]

variable [∀ i, NeZero (k i)]

/-- Confidence and hard bit budget for the estimator driven by actual fair
bits. The recursion level controls stochastic error and the grid controls
operator error. -/
theorem scalarPlannerFairQuery_correct (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1)
    (b : ℕ) (x : ScalarPlannerState n) (r : ℕ) (h p : ℝ)
    (hh : 0 < h) (hp : 0 < p) (hp1 : p < 1) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (hprec : 25 * (scalarPlannerWeight y x.1)^2 * (1/2 : ℝ)^r ≤ (h/2)^2 / 64)
    (hgrid : scalarPlannerWeight y x.1 * ((10*(n:ℝ)+4)/(3*((2^b : ℕ):ℝ))) ≤ h/4) :
    let μ := multilevelTreeLaw (plannerFairSeedLaw n b) r
    let Q := scalarPlannerFairQuery y b x r p H
    Measurable (fun bits => (Q bits).value) ∧
      (Measure.pi (fun _ : Fin (confidenceCopyCount p H) => μ)).real
        {bits | h < |(Q bits).value - scalarPlannerValue y hy x|} ≤ p ∧
      ∀ bits, (Q bits).copies ≤ confidenceCopyCount p H ∧
        (Q bits).work ≤ confidenceCopyCount p H * (4 * 16^r+1) + 10 * (confidenceCopyCount p H+1)^2 + 2 ∧
        scalarPlannerFairReads b r bits ≤ confidenceCopyCount p H * (4*16^r) * ((3*n+2)*b) := by
  dsimp only
  let m := confidenceCopyCount p H
  let v := scalarPlannerValue y hy x
  let μ := multilevelTreeLaw (plannerUniformSeedLaw n) r
  let μb := multilevelTreeLaw (plannerFairSeedLaw n b) r
  let ν := multilevelTreeLaw (plannerRoundedSeedLaw n (2^b) (by positivity)) r
  let R := scalarPlannerQueryAtLevel y x r p H
  let B := {seed | h < |(R seed).value-v|}
  have hi := scalarPlannerQueryAtLevel_correct y hy hcap x r h p hh hp hp1 H
    (hprec.trans (by nlinarith [sq_nonneg h]))
  have hB : MeasurableSet B := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (hi.1.sub measurable_const))
  have hr := measurePreserving_multilevelTreeMap (measurePreserving_plannerRoundSeed n (2^b) (by positivity)) r
  have hb := measurePreserving_multilevelTreeMap (measurePreserving_plannerFairSeedReal n b) r
  have hrπ := measurePreserving_pi (fun _ : Fin m => μ) (fun _ : Fin m => ν) (fun _ => hr)
  have hbπ := measurePreserving_pi (fun _ : Fin m => μb) (fun _ : Fin m => ν) (fun _ => hb)
  have hround := scalarPlannerRoundedQuery_correct y hy hcap (2^b) (by positivity) x r h p hh hp hp1 H hprec hgrid
  refine ⟨hi.1.comp hbπ.measurable, ?_, ?_⟩
  · have hEq : (Measure.pi (fun _ : Fin m => μb)).real
        {bits | h < |(scalarPlannerFairQuery y b x r p H bits).value-v|} =
        (Measure.pi (fun _ : Fin m => μ)).real
          {seed | h < |(scalarPlannerRoundedQuery y (2^b) (by positivity) x r p H seed).value-v|} := by
      have hpre : {seed | h < |(scalarPlannerRoundedQuery y (2^b) (by positivity) x r p H seed).value-v|} =
          (fun seed j => multilevelTreeMap (plannerRoundSeed (2^b) (by positivity)) r (seed j)) ⁻¹' B := by
        ext seed
        simp only [Set.mem_setOf_eq, Set.mem_preimage, B, R, scalarPlannerRoundedQuery_eq_map]
      change (Measure.pi (fun _ : Fin m => μb)).real
        ((fun bits j => multilevelTreeMap (plannerFairSeedReal b) r (bits j)) ⁻¹' B) = _
      rw [hpre, Measure.real, Measure.real, ← Measure.map_apply hbπ.measurable hB, hbπ.map_eq,
        ← Measure.map_apply hrπ.measurable hB, hrπ.map_eq]
    exact hEq.le.trans hround.2.1
  · intro bits
    have hq := hi.2.2 (fun j => multilevelTreeMap (plannerFairSeedReal b) r (bits j))
    exact ⟨hq.1,hq.2,scalarPlannerFairReads_le b r bits⟩

end ProphetSecretary.Statistics
