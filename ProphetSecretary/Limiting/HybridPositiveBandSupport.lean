import ProphetSecretary.Limiting.HybridBellmanIdentity
import ProphetSecretary.Model.StabilityBands

/-!
# Positive-band duration and fixed-base horizon support

For any nonnegative duration weight, an exact finite-hybrid optimizer on a
continuation level at least 3wb/4 has duration bounded below by
the paper's positiveBandDuration, using only tails above b/4. Holding this base
policy fixed while increasing the remaining horizon gives the required support
inequality; adding Poisson intensity only increases the actual value.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma FiniteIntensityHybridInstance.restrictIndividuals_tailCount_le (B : FiniteIntensityHybridInstance n)
    (A : Finset (Fin n)) (b : ℝ) : (B.restrictIndividuals A).tailCount b ≤ B.tailCount b :=
  add_le_add (B.individuals.tailCount_restrictTo_le A b) le_rfl

/-- The bound is valid for every competing policy with the stated objective;
optimality is used only when it is instantiated below at a base horizon. -/
theorem RandomizedHybridPolicy.duration_ge_positiveValue (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {H w c b L d : ℝ}
    (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H) (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    (hTail : B.tailCount (b/4) ≤ L) (hd : d ≤ c) (hObj : 3*w*b/4 ≤ π.scalarObjective B w d) :
    Model.positiveBandDuration H w c b L ≤ π.expectedDuration B := by
  have hb4 : 0 ≤ b/4 := by positivity
  have hR := π.expectedReward_le_cutoff_add_tailCount B hb4 (by simpa only [ha,NNReal.coe_zero] using hb4)
  have hT := π.expectedDuration_nonnegative B
  have hL0 : 0 ≤ L := (B.tailCount_nonnegative _).trans hTail
  have hProd : (B.cap : ℝ)*B.tailCount (b/4) ≤ H*L :=
    mul_le_mul hCap hTail (B.tailCount_nonnegative _) hH
  have hR' : π.expectedReward B ≤ b/4+(2*π.expectedDuration B)*(H*L) := by
    apply hR.trans
    apply add_le_add le_rfl
    calc
      _ = (2*π.expectedDuration B)*((B.cap : ℝ)*B.tailCount (b/4)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hProd (mul_nonneg (by norm_num) hT)
  have hJ : π.scalarObjective B w d ≤ w*b/4+π.expectedDuration B*(2*w*H*L+c) := by
    rw [π.scalarObjective_eq]
    calc
      _ ≤ w*(b/4+(2*π.expectedDuration B)*(H*L))+c*π.expectedDuration B :=
        add_le_add (mul_le_mul_of_nonneg_left hR' hw.le) (mul_le_mul_of_nonneg_right hd hT)
      _ = _ := by ring
  unfold Model.positiveBandDuration
  apply (div_le_iff₀ (show (0 : ℝ) < 2*(2*w*H*L+c) by positivity)).mpr
  nlinarith only [hObj,hJ]

/-- The base optimizer is evaluated under its original scaled intensity;
only its duration coefficient is first changed. This is not differentiation
after reoptimizing the policy. -/
theorem FiniteIntensityHybridInstance.continuationValue_support (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) {u v : ℝ≥0} (huv : u ≤ v) :
    B.continuationValue w c u+c*((v : ℝ)-(u : ℝ))*
      ((B.remainingHorizon u).valueThresholdPolicy hw.le (mul_nonneg hc u.property)).expectedDuration (B.remainingHorizon u) ≤
      B.continuationValue w c v := by
  let R := B.remainingHorizon u
  let π := R.valueThresholdPolicy hw.le (mul_nonneg hc u.property)
  have hOpt : π.scalarObjective R w (c*(u : ℝ)) = B.continuationValue w c u :=
    R.valueThresholdPolicy_optimal ha hw (mul_nonneg hc u.property)
  have hRaise : π.scalarObjective R w (c*(u : ℝ))+c*((v : ℝ)-(u : ℝ))*π.expectedDuration R =
      π.scalarObjective R w (c*(v : ℝ)) := by
    rw [π.scalarObjective_eq,π.scalarObjective_eq]
    ring
  have hUpper : π.scalarObjective R w (c*(v : ℝ)) ≤ B.continuationValue w c v :=
    (R.scalarObjective_le_value π w (c*(v : ℝ))).trans
      (B.remainingHorizon_value_mono_intensity huv hw.le (mul_nonneg hc v.property))
  change B.continuationValue w c u+c*((v : ℝ)-(u : ℝ))*π.expectedDuration R ≤ _
  rw [← hOpt,hRaise]
  exact hUpper

lemma retainedClockState_antitone (u : Fin n → ℝ) (candidate : Option (Fin n)) :
    Antitone (retainedClockState u · candidate) := by
  intro t s hts
  have hA : Model.unseen (Model.history Finset.univ (fun _ => 0) u s) ⊆
      Model.unseen (Model.history Finset.univ (fun _ => 0) u t) := by
    intro j hj
    have hs : s ≤ u j := by simpa [Model.unseen,Model.history,not_lt] using hj
    have ht : t ≤ u j := hts.trans hs
    simpa [Model.unseen,Model.history,not_lt] using ht
  cases candidate with
  | none => exact hA
  | some i => exact Finset.erase_subset_erase i hA

end ProphetSecretary.Limiting
