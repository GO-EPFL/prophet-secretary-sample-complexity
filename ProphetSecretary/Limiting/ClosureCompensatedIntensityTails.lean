import ProphetSecretary.Limiting.ClosureCompensatedIntensityFinite
import ProphetSecretary.Limiting.ExtendedTailLevels
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Structural tail clauses for actual residual compensated intensity tilts

The independent finite laws lie between three quarters and five quarters
of the original laws on every measurable event. This gives uniform positive
tail bounds, residual rarity and dense below-reserve supply. Each fixed label
is eventually before the residual schedule and retains its original weak law.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma compensatedResidualOffers_padded_before (P : Model.Instance n) (N : ℕ) {S : Set ℝ}
    (hS : MeasurableSet S) (θ : ℝ) (hθ : |θ|≤1/4) (j : ℕ) (hj : j<N) :
    labeledPaddedLaw (compensatedResidualOffers P N S hS θ hθ) j=labeledPaddedLaw P j := by
  apply ProbabilityMeasure.toMeasure_injective
  by_cases hjn : j<n
  · rw [labeledPaddedLaw_of_lt _ hjn,labeledPaddedLaw_of_lt P hjn]
    exact compensatedResidualOffers_law_before P N hS θ hθ ⟨j,hjn⟩ hj
  · rw [labeledPaddedLaw_of_ge _ (not_lt.mp hjn),labeledPaddedLaw_of_ge P (not_lt.mp hjn)]

lemma compensatedResidualOffers_event_real_le (P : Model.Instance n) (N : ℕ) {S E : Set ℝ}
    (hS : MeasurableSet S) (θ : ℝ) (hθ : |θ|≤1/4) (j : Fin n) (hE : MeasurableSet E) :
    ((compensatedResidualOffers P N S hS θ hθ).law j).real E≤(5/4 : ℝ)*(P.law j).real E := by
  have h := Measure.le_iff.mp (compensatedResidualOffers_measure_bounds P N hS θ hθ j).2 E hE
  rw [Measure.smul_apply,smul_eq_mul] at h
  have hReal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by norm_num : (0 : ℝ)≤5/4),Measure.real] using hReal

lemma compensatedResidualOffers_padded_tail_le (P : Model.Instance n) (N : ℕ) {S : Set ℝ}
    (hS : MeasurableSet S) (θ : ℝ) (hθ : |θ|≤1/4) (j : ℕ) {d : ℝ} (hd : 0≤d) :
    (labeledPaddedLaw (compensatedResidualOffers P N S hS θ hθ) j : Measure ℝ).real (Ioi d)≤
      (5/4 : ℝ)*(labeledPaddedLaw P j : Measure ℝ).real (Ioi d) := by
  by_cases hj : j<n
  · rw [labeledPaddedLaw_of_lt _ hj,labeledPaddedLaw_of_lt P hj]
    exact compensatedResidualOffers_event_real_le P N hS θ hθ ⟨j,hj⟩ measurableSet_Ioi
  · rw [labeledPaddedLaw_of_ge _ (not_lt.mp hj),labeledPaddedLaw_of_ge P (not_lt.mp hj)]
    simp [Measure.real,Measure.dirac_apply',not_lt.mpr hd]

lemma compensatedResidualOffers_tailCount_le (P : Model.Instance n) (N : ℕ) {S : Set ℝ}
    (hS : MeasurableSet S) (θ : ℝ) (hθ : |θ|≤1/4) (d : ℝ) :
    (compensatedResidualOffers P N S hS θ hθ).tailCount d≤(5/4 : ℝ)*P.tailCount d := by
  change (∑ j, ((compensatedResidualOffers P N S hS θ hθ).law j).real (Ioi d))≤(5/4 : ℝ)*∑ j, (P.law j).real (Ioi d)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => compensatedResidualOffers_event_real_le P N hS θ hθ j measurableSet_Ioi)

lemma compensatedResidualOffers_extended_lower (P : Model.Instance n) (N : ℕ) {S : Set ℝ}
    (hS : MeasurableSet S) (θ : ℝ) (hθ : |θ|≤1/4) (d : ℝ) :
    ENNReal.ofReal (3/4)*extendedTailCount P d≤extendedTailCount (compensatedResidualOffers P N S hS θ hθ) d := by
  change ENNReal.ofReal (3/4)*(∑ j, P.law j (Ioi d))≤∑ j, (compensatedResidualOffers P N S hS θ hθ).law j (Ioi d)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := Measure.le_iff.mp (compensatedResidualOffers_measure_bounds P N hS θ hθ j).1 (Ioi d) measurableSet_Ioi
  simpa only [Measure.smul_apply,smul_eq_mul] using h

lemma LabeledBandConvergence.compensated_structural_clauses {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    {S : Set ℝ} (hS : MeasurableSet S) (θ : ℝ) (hθ : |θ|≤1/4) :
    (∀ i, Tendsto (fun m => labeledPaddedLaw (compensatedResidualOffers (P m) (Ns m) S hS θ hθ) i)
      atTop (𝓝 (B.individuals i))) ∧
    (∀ d : ℝ, (B.terminal : ℝ)<d → ∀ ε>(0 : ℝ), ∃ N : ℕ,
      ∀ᶠ m in atTop, ∀ j, N≤j →
        (labeledPaddedLaw (compensatedResidualOffers (P m) (Ns m) S hS θ hθ) j : Measure ℝ).real (Ioi d)<ε) ∧
    (∀ x : ℝ, 0≤x → x<(B.terminal : ℝ) →
      Tendsto (fun m => extendedTailCount (compensatedResidualOffers (P m) (Ns m) S hS θ hθ) x) atTop (𝓝 ⊤)) ∧
    (∀ d : ℝ, (B.terminal : ℝ)<d → ∃ K : ℝ, 0≤K ∧ ∀ m,
      (compensatedResidualOffers (P m) (Ns m) S hS θ hθ).tailCount d≤K) := by
  constructor
  · intro i
    apply (h.individual_weak i).congr'
    filter_upwards [hNs (eventually_gt_atTop i)] with m hm
    exact (compensatedResidualOffers_padded_before (P m) (Ns m) hS θ hθ i hm).symm
  constructor
  · intro d hd ε hε
    obtain ⟨N,hRare⟩ := h.rare d hd (ε/2) (by positivity)
    refine ⟨N,?_⟩
    filter_upwards [hRare] with m hm j hj
    have hBound := compensatedResidualOffers_padded_tail_le (P m) (Ns m) hS θ hθ j
      (B.terminal.property.trans hd.le)
    have hSmall := mul_lt_mul_of_pos_left (hm j hj) (by norm_num : (0 : ℝ)<5/4)
    exact hBound.trans_lt (hSmall.trans (by linarith only [hε]))
  constructor
  · intro x _hx hxa
    have hOld := h.below_reserve x _hx hxa
    have hPositive : ENNReal.ofReal (3/4)≠0 := ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)
    have hProduct : Tendsto (fun m => ENNReal.ofReal (3/4)*extendedTailCount (P m) x) atTop (𝓝 ⊤) := by
      simpa only [ENNReal.mul_top hPositive] using
        ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (3/4)) hOld (Or.inl (by simp : (⊤ : ENNReal)≠0))
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [hProduct.eventually (Ioi_mem_nhds ha)] with m hm
      exact hm.trans_le (compensatedResidualOffers_extended_lower (P m) (Ns m) hS θ hθ x)
    · intro a ha
      exact (not_lt_of_ge le_top ha).elim
  · intro d hd
    obtain ⟨K,hK,hBound⟩ := h.above_reserve d hd
    refine ⟨(5/4 : ℝ)*K,by positivity,?_⟩
    intro m
    exact (compensatedResidualOffers_tailCount_le (P m) (Ns m) hS θ hθ d).trans
      (mul_le_mul_of_nonneg_left (hBound m) (by norm_num))

end ProphetSecretary.Limiting
