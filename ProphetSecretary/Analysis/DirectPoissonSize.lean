import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# An explicit fixed virtual-offer count for direct approximants

For base intensity R at refinement index m, choose
N = ceil(2R + (m+1)²R² + m+1). Then N is positive, R/N≤1/2,
and R²/N≤1/(m+1)². The count is chosen from the base intensity
and remains fixed throughout each likelihood perturbation family.
-/

open Filter
open scoped NNReal Topology
namespace ProphetSecretary.Analysis

noncomputable def directPoissonMultiplicity (R : ℝ≥0) (m : ℕ) : ℕ :=
  Nat.ceil (2*(R : ℝ)+((m : ℝ)+1)^2*(R : ℝ)^2+(m : ℝ)+1)

lemma directPoissonMultiplicity_lower_bounds (R : ℝ≥0) (m : ℕ) :
    m+1≤directPoissonMultiplicity R m ∧
      2*(R : ℝ)≤directPoissonMultiplicity R m ∧
      ((m : ℝ)+1)^2*(R : ℝ)^2≤directPoissonMultiplicity R m := by
  have hCeil := Nat.le_ceil (2*(R : ℝ)+((m : ℝ)+1)^2*(R : ℝ)^2+(m : ℝ)+1)
  change 2*(R : ℝ)+((m : ℝ)+1)^2*(R : ℝ)^2+(m : ℝ)+1≤(directPoissonMultiplicity R m : ℝ) at hCeil
  have hProduct := mul_nonneg (sq_nonneg ((m : ℝ)+1)) (sq_nonneg (R : ℝ))
  have hR := R.coe_nonneg
  have hm := Nat.cast_nonneg (α:=ℝ) m
  have hFirst : (m : ℝ)+1≤directPoissonMultiplicity R m := by linarith only [hCeil,hProduct,hR]
  refine ⟨by exact_mod_cast hFirst,?_,?_⟩ <;> linarith only [hCeil,hProduct,hR,hm]

lemma directPoissonMultiplicity_positive (R : ℝ≥0) (m : ℕ) : 0<directPoissonMultiplicity R m := by
  have h := (directPoissonMultiplicity_lower_bounds R m).1
  omega

lemma rate_le_directPoissonMultiplicity (R : ℝ≥0) (m : ℕ) :
    R≤(directPoissonMultiplicity R m : ℝ≥0) := by
  have h := (directPoissonMultiplicity_lower_bounds R m).2.1
  have hR := R.coe_nonneg
  exact_mod_cast (show (R : ℝ)≤directPoissonMultiplicity R m by linarith only [h,hR])

lemma directPoissonProbability_le_half (R : ℝ≥0) (m : ℕ) :
    (R : ℝ)/(directPoissonMultiplicity R m : ℝ)≤1/2 := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr (directPoissonMultiplicity_positive R m))).mpr
  have h := (directPoissonMultiplicity_lower_bounds R m).2.1
  linarith only [h]

lemma directPoisson_square_error_le (R : ℝ≥0) (m : ℕ) :
    (R : ℝ)^2/(directPoissonMultiplicity R m : ℝ)≤1/((m : ℝ)+1)^2 := by
  apply (div_le_div_iff₀ (Nat.cast_pos.mpr (directPoissonMultiplicity_positive R m))
    (sq_pos_of_pos (by positivity : (0 : ℝ)<(m : ℝ)+1))).mpr
  have h := (directPoissonMultiplicity_lower_bounds R m).2.2
  nlinarith only [h]

lemma directPoissonMultiplicity_tendsto (R : ℕ → ℝ≥0) :
    Tendsto (fun m => directPoissonMultiplicity (R m) m) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro m
  exact (Nat.le_succ m).trans (directPoissonMultiplicity_lower_bounds (R m) m).1

lemma directPoisson_square_error_tendsto (R : ℕ → ℝ≥0) :
    Tendsto (fun m => (R m : ℝ)^2/(directPoissonMultiplicity (R m) m : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have hUpper : Tendsto (fun m : ℕ => 1/((m : ℝ)+1)^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_pow,one_pow,zero_pow (by norm_num : (2 : ℕ)≠0)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).pow 2
  exact squeeze_zero (fun m => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    (fun m => directPoisson_square_error_le (R m) m) hUpper

end ProphetSecretary.Analysis
