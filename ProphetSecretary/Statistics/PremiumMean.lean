import ProphetSecretary.Model.BellmanResidual

/-!
# Expected unstopped Bellman premiums

Paper correspondence: `upstat:premiummean`. An always-wait policy reaches every
arrival. Under a deterministic zero-valued evaluation instance its design action loss
is zero, so the proved cross-law residual identity exactly telescopes the positive
premiums of every design marginal. The zero instance is auxiliary and may have zero
expected maximum.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

/-- An auxiliary nonnegative finite instance with every offer equal to zero. -/
noncomputable def zeroInstance (n : ℕ) : Instance n where
  law _ := Measure.dirac 0
  probability _ := inferInstance
  nonnegative _ := by simp

lemma zeroInstance_integrable (n : ℕ) :
    Integrable Instance.maximum (zeroInstance n).valuesLaw := by
  apply Instance.integrable_maximum
  intro i
  exact integrable_dirac (by simp)

lemma zeroInstance_restrictTo {n : ℕ} (A : Finset (Fin n)) :
    (zeroInstance n).restrictTo A = zeroInstance A.card := by
  apply Instance.eq_of_law_eq
  rfl

variable {n : ℕ}

noncomputable def Instance.clockPremium (Q : Instance n) (w c : ℝ) (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  positivePremium (Q.law i) w (Q.continuationAtArrival w c (fun _ => 0) u i)

/-- Following all arrival clocks without stopping defines an analytical positive sum. -/
noncomputable def Instance.unstoppedPremium (Q : Instance n) (w c : ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ i, Q.clockPremium w c u i

lemma Instance.clockPremium_nonnegative (Q : Instance n) (w c : ℝ) (u : Fin n → ℝ) (i : Fin n) :
    0 ≤ Q.clockPremium w c u i := positivePremium_nonnegative _ _ _

lemma Instance.unstoppedPremium_nonnegative (Q : Instance n) (w c : ℝ) (u : Fin n → ℝ) :
    0 ≤ Q.unstoppedPremium w c u := Finset.sum_nonneg (fun i _ => Q.clockPremium_nonnegative w c u i)

lemma Instance.transitionResidual_zero (Q : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (u : Fin n → ℝ) (i : Fin n) :
    Q.transitionResidual (zeroInstance n) w c u i = Q.clockPremium w c u i := by
  let θ := Q.continuationAtArrival w c (fun _ => 0) u i
  have hθ : 0 ≤ θ := Q.continuationAtArrival_nonnegative hQ hw hc _ u i
  change positivePremium (Q.law i) w θ - positivePremium (Measure.dirac 0) w θ = _
  have hzero : positivePremium (Measure.dirac 0) w θ = 0 := by
    simp [positivePremium, max_eq_right (neg_nonpos.mpr hθ)]
  rw [hzero, sub_zero]
  rfl

lemma Instance.measurable_clockPremium (Q : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) : Measurable (fun u => Q.clockPremium w c u i) :=
  (positivePremium_continuous (Q.law i) (Q.integrable_maximum_iff.mp hQ i) w).measurable.comp
    (Q.measurable_continuationAtArrival hQ hw hc (fun _ => measurable_const) (fun j => measurable_pi_apply j) i)

lemma Instance.measurable_unstoppedPremium (Q : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) : Measurable (Q.unstoppedPremium w c) :=
  Finset.measurable_sum _ (fun i _ => Q.measurable_clockPremium hQ hw hc i)

lemma Instance.unstoppedPremium_le_firstMoment (Q : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (u : Fin n → ℝ) :
    Q.unstoppedPremium w c u ≤ w * Q.totalFirstMoment := by
  calc
    _ ≤ ∑ i : Fin n, w * ∫ x, x ∂Q.law i := by
      apply Finset.sum_le_sum
      intro i _
      exact positivePremium_le_firstMoment (Q.law i) (Q.integrable_maximum_iff.mp hQ i) (Q.nonnegative i) hw
        (Q.continuationAtArrival_nonnegative hQ hw hc _ u i)
    _ = _ := by simp only [Instance.totalFirstMoment, Finset.mul_sum]

lemma Instance.integrable_unstoppedPremium_pow (Q : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (p : ℕ) :
    Integrable (fun u => Q.unstoppedPremium w c u ^ p) (Instance.clocksLaw n) := by
  apply Integrable.of_bound ((Q.measurable_unstoppedPremium hQ hw hc).pow_const p).aestronglyMeasurable
    ((w * Q.totalFirstMoment) ^ p)
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Q.unstoppedPremium_nonnegative w c u) p)]
  exact pow_le_pow_left₀ (Q.unstoppedPremium_nonnegative w c u) (Q.unstoppedPremium_le_firstMoment hQ hw.le hc u) p

lemma waiting_clockConditionalReach (P : Instance n) (u : Fin n → ℝ) (i : Fin n) (hi : u i ≤ 1) :
    (RandomizedPolicy.waiting n).rule.clockConditionalReach P (RandomizedPolicy.waiting n).seedLaw u i = 1 := by
  have hp : (P.valuesLaw.prod (RandomizedPolicy.waiting n).seedLaw).real Set.univ = 1 := probReal_univ
  simpa [Policy.clockConditionalReach, Policy.Reaches, RandomizedPolicy.waiting,
    Policy.stoppingTime, Policy.stopTimes, Policy.accepted, Policy.action, hi] using hp

lemma waiting_expectedDesignActionLoss_zero (Q : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (RandomizedPolicy.waiting n).expectedReachedDesignActionLoss Q (zeroInstance n) w c = 0 := by
  have hx : ∀ᵐ x ∂(zeroInstance n).valuesLaw, ∀ i, x i = 0 := by
    rw [ae_all_iff]
    intro i
    have hi0 : ∀ᵐ x ∂(zeroInstance n).law i, x = 0 := by simp [zeroInstance]
    exact (measurePreserving_eval (zeroInstance n).law i).quasiMeasurePreserving.ae hi0
  have hv : MeasurePreserving (fun ω : (RandomizedPolicy.waiting n).World => ω.1)
      ((zeroInstance n).worldLaw (RandomizedPolicy.waiting n).seedLaw) (zeroInstance n).valuesLaw := measurePreserving_fst
  apply integral_eq_zero_of_ae
  filter_upwards [hv.quasiMeasurePreserving.ae hx] with ω hω
  unfold Policy.reachedBellmanLoss
  apply Finset.sum_eq_zero
  intro i _
  have hθ := Q.continuationAtArrival_nonnegative hQ hw hc ω.1 ω.2.1 i
  have hlocal : (RandomizedPolicy.waiting n).rule.arrivalBellmanLoss Q w c ω.2.2 ω.1 ω.2.1 i = 0 := by
    change max (w * ω.1 i) (Q.continuationAtArrival w c ω.1 ω.2.1 i) -
      Q.continuationAtArrival w c ω.1 ω.2.1 i = 0
    rw [hω i, mul_zero, max_eq_right hθ, sub_self]
  split_ifs <;> simp only [hlocal]

/-- Exact finite premium-mean identity, including zero-maximum auxiliary instances. -/
theorem Instance.integral_unstoppedPremium (Q : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ u, Q.unstoppedPremium w c u ∂Instance.clocksLaw n) = optimalScalarValue Q w c - c := by
  have h := (RandomizedPolicy.waiting n).bellman_residualIdentity_clocks Q (zeroInstance n)
    hQ (zeroInstance_integrable n) hw hc
  rw [RandomizedPolicy.waiting_scalarObjective, waiting_expectedDesignActionLoss_zero Q hQ hw.le hc, add_zero] at h
  apply Eq.symm
  apply h.trans
  apply integral_congr_ae
  filter_upwards [Instance.clocks_mem_unitInterval (n := n)] with u hu
  apply Finset.sum_congr rfl
  intro i _
  rw [waiting_clockConditionalReach (zeroInstance n) u i (hu i).2, one_mul,
    Q.transitionResidual_zero hQ hw.le hc]

end ProphetSecretary.Model
