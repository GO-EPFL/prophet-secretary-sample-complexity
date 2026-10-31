import ProphetSecretary.Statistics.EpsilonSampleUpperBound
import ProphetSecretary.Model.SampleComplexityMinimum
import Mathlib.Analysis.Asymptotics.Defs

/-!
# From feasible-budget lower estimates to sample-complexity asymptotics

The explicit lower and upper constants precede epsilon. Finiteness and
attainment of the extended-natural minimum justify using its natural value
in the real asymptotic statement. The lower estimate is an explicit input
in this assembly lemma. Paper correspondence: `thm:theta-main`.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

theorem sampleComplexity_bounds_of_feasible_lower
    (hLower : ∃ a eps0 : ℝ, 0<a ∧ 0<eps0 ∧ ∀ eps : ℝ, eps∈Ioo (0 : ℝ) eps0 →
      ∀ k : ℕ, FeasibleBudget eps k → a/eps≤(k : ℝ)) :
    ∃ a A eps0 : ℝ, 0<a ∧ 0<A ∧ 0<eps0 ∧ ∀ eps : ℝ, eps∈Ioo (0 : ℝ) eps0 →
      sampleComplexity eps<⊤ ∧ a/eps≤((sampleComplexity eps).toNat : ℝ) ∧
        ((sampleComplexity eps).toNat : ℝ)≤A/eps := by
  obtain ⟨a,eta,ha,hEta,hLow⟩ := hLower
  obtain ⟨K,hK,hUpper⟩ := epsilon_sample_upper_bound
  refine ⟨a,K+1,min 1 eta,ha,by linarith only [hK],lt_min (by norm_num) hEta,?_⟩
  intro eps hEps
  have hSmall : eps<1 := hEps.2.trans_le (min_le_left _ _)
  have hEtaSmall : eps<eta := hEps.2.trans_le (min_le_right _ _)
  have hU := hUpper eps hEps.1
  have hNonempty : ∃ k : ℕ, FeasibleBudget eps k := ⟨_,hU.1⟩
  have hMin := sampleComplexity_toNat_feasible hNonempty
  refine ⟨lt_top_iff_ne_top.mpr (sampleComplexity_ne_top hNonempty),hLow eps ⟨hEps.1,hEtaSmall⟩ _ hMin,?_⟩
  have hBudget : ((sampleComplexity eps).toNat : ℝ)≤Nat.ceil (K/eps) :=
    by exact_mod_cast sampleComplexity_toNat_le hU.1
  exact hBudget.trans (hU.2.2 hSmall)

theorem sampleComplexity_theta_of_feasible_lower
    (hLower : ∃ a eps0 : ℝ, 0<a ∧ 0<eps0 ∧ ∀ eps : ℝ, eps∈Ioo (0 : ℝ) eps0 →
      ∀ k : ℕ, FeasibleBudget eps k → a/eps≤(k : ℝ)) :
    (fun eps : ℝ => ((sampleComplexity eps).toNat : ℝ)) =Θ[𝓝[>] (0 : ℝ)] (fun eps => 1/eps) := by
  obtain ⟨a,A,eps0,ha,_hA,hEps0,hBound⟩ := sampleComplexity_bounds_of_feasible_lower hLower
  have hSmall : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), eps<eps0 :=
    (gt_mem_nhds hEps0).filter_mono nhdsWithin_le_nhds
  have hPositive : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), 0<eps := self_mem_nhdsWithin
  constructor
  · apply Asymptotics.IsBigO.of_bound A
    filter_upwards [hPositive,hSmall] with eps hPos hNear
    have h := (hBound eps ⟨hPos,hNear⟩).2.2
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (sampleComplexity eps).toNat),
      abs_of_pos (inv_pos.mpr hPos),div_eq_mul_inv,one_mul] using h
  · apply Asymptotics.IsBigO.of_bound (1/a)
    filter_upwards [hPositive,hSmall] with eps hPos hNear
    have h := (hBound eps ⟨hPos,hNear⟩).2.1
    have hScale := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ha.le)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (sampleComplexity eps).toNat),
      abs_of_pos (inv_pos.mpr hPos),one_div,div_eq_mul_inv,←mul_assoc,
      inv_mul_cancel₀ ha.ne',one_mul] using hScale

end ProphetSecretary.Statistics
