import ProphetSecretary.Model.BellmanResidual

/-!
# Residual comparison before averaging training

Paper correspondence: `upstat:comparison`. A realized reach set is a chronological
prefix, so its signed residual is the full sum minus one chronological suffix.
The resulting factor two is pathwise and does not condition on a data-selected weight.
The statistical moment estimate for the suffix envelope is a separate dependency.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics

variable {n : ℕ}

/-- `none` denotes the full sum; a candidate denotes the suffix beginning at its clock. -/
noncomputable def suffixSum (u ξ : Fin n → ℝ) : Option (Fin n) → ℝ
  | none => ∑ i, ξ i
  | some j => ∑ i, if u j ≤ u i then ξ i else 0

/-- Absolute suffix maximum, including the full sum and valid for the empty instance. -/
noncomputable def suffixEnvelope (u ξ : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' ⟨none, Finset.mem_univ _⟩ (fun j : Option (Fin n) => |suffixSum u ξ j|)

lemma le_suffixEnvelope (u ξ : Fin n → ℝ) (j : Option (Fin n)) :
    |suffixSum u ξ j| ≤ suffixEnvelope u ξ :=
  Finset.le_sup' (fun q : Option (Fin n) => |suffixSum u ξ q|) (Finset.mem_univ j)

lemma suffixEnvelope_nonnegative (u ξ : Fin n → ℝ) : 0 ≤ suffixEnvelope u ξ :=
  (abs_nonneg (suffixSum u ξ none)).trans (le_suffixEnvelope u ξ none)

lemma suffixEnvelope_le_sum_abs (u ξ : Fin n → ℝ) : suffixEnvelope u ξ ≤ ∑ i, |ξ i| := by
  apply Finset.sup'_le
  intro j _
  cases j with
  | none => exact Finset.abs_sum_le_sum_abs _ _
  | some j =>
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact le_rfl
    · simp only [abs_zero]
      exact abs_nonneg (ξ i)

/-- A prefix is full sum minus a suffix, even at tied clocks and at arbitrary cutoffs. -/
lemma abs_prefixSum_le_twice_suffixEnvelope (u ξ : Fin n → ℝ) (t : ℝ) :
    |∑ i, if u i ≤ t then ξ i else 0| ≤ 2 * suffixEnvelope u ξ := by
  let F := Finset.univ.filter fun i => t < u i
  have htotal : (∑ i, if u i ≤ t then ξ i else 0) +
      (∑ i, if t < u i then ξ i else 0) = ∑ i, ξ i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : u i ≤ t
    · simp [hi, not_lt_of_ge hi]
    · simp [hi, lt_of_not_ge hi]
  by_cases hF : F.Nonempty
  · obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image F u hF
    have hjt : t < u j := (Finset.mem_filter.mp hj).2
    have hiff (i : Fin n) : t < u i ↔ u j ≤ u i := by
      constructor
      · intro hi
        exact hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      · intro hi
        exact hjt.trans_le hi
    have htail : (∑ i, if t < u i then ξ i else 0) = suffixSum u ξ (some j) := by
      simp only [suffixSum, hiff]
    have heq : (∑ i, if u i ≤ t then ξ i else 0) = suffixSum u ξ none - suffixSum u ξ (some j) := by
      rw [htail] at htotal
      dsimp [suffixSum] at htotal ⊢
      linarith
    rw [heq]
    calc
      _ ≤ |suffixSum u ξ none| + |suffixSum u ξ (some j)| := abs_sub _ _
      _ ≤ suffixEnvelope u ξ + suffixEnvelope u ξ :=
        add_le_add (le_suffixEnvelope u ξ none) (le_suffixEnvelope u ξ (some j))
      _ = _ := by ring
  · have htail : (∑ i, if t < u i then ξ i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : ¬t < u i := fun hi => hF ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      simp only [hi, ite_false]
    rw [htail, add_zero] at htotal
    rw [htotal]
    exact (le_suffixEnvelope u ξ none).trans (by linarith [suffixEnvelope_nonnegative u ξ])

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_suffixEnvelope {u ξ : Ω → Fin n → ℝ}
    (hu : ∀ i, Measurable fun ω => u ω i) (hξ : ∀ i, Measurable fun ω => ξ ω i) :
    Measurable fun ω => suffixEnvelope (u ω) (ξ ω) := by
  have hm : Measurable ((Finset.univ : Finset (Option (Fin n))).sup' ⟨none, Finset.mem_univ _⟩
      (fun j => fun ω => |suffixSum (u ω) (ξ ω) j|)) := by
    apply Finset.measurable_sup'
    intro j _
    apply continuous_abs.measurable.comp
    cases j with
    | none => exact Finset.measurable_sum _ (fun i _ => hξ i)
    | some j =>
      apply Finset.measurable_sum
      intro i _
      exact Measurable.ite (measurableSet_le (hu j) (hu i)) (hξ i) measurable_const
  convert hm using 1
  funext ω
  exact (Finset.sup'_apply ⟨none, Finset.mem_univ _⟩
    (fun j : Option (Fin n) => fun ω => |suffixSum (u ω) (ξ ω) j|) ω).symm

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.residualSuffixEnvelope (Q P : Instance n) (w c : ℝ) (u : Fin n → ℝ) : ℝ :=
  ProphetSecretary.Statistics.suffixEnvelope u (Q.transitionResidual P w c u)

lemma Instance.measurable_residualSuffixEnvelope (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Measurable (Q.residualSuffixEnvelope P w c) :=
  ProphetSecretary.Statistics.measurable_suffixEnvelope (fun i => measurable_pi_apply i)
    (fun i => Q.measurable_transitionResidual P hQ hP hw hc (fun j => measurable_pi_apply j) i)

lemma Instance.integrable_residualSuffixEnvelope (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (Q.residualSuffixEnvelope P w c) (Instance.clocksLaw n) := by
  apply Integrable.of_bound (Q.measurable_residualSuffixEnvelope P hQ hP hw hc).aestronglyMeasurable
    (w * (Q.totalFirstMoment + P.totalFirstMoment))
  filter_upwards [] with u
  have h0 : 0 ≤ Q.residualSuffixEnvelope P w c u := ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  apply (ProphetSecretary.Statistics.suffixEnvelope_le_sum_abs _ _).trans
  calc
    (∑ i, |Q.transitionResidual P w c u i|) ≤
        ∑ i, w * ((∫ x, x ∂Q.law i) + ∫ x, x ∂P.law i) :=
      Finset.sum_le_sum (fun i _ => Q.abs_transitionResidual_le P hQ hP hw.le hc u i)
    _ = _ := by simp only [Instance.totalFirstMoment, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma Policy.abs_reachedTransitionResidual_le_suffix {Seed : Type*} (π : Policy Seed n)
    (Q P : Instance n) (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) :
    |π.reachedTransitionResidual Q P w c r x u| ≤ 2 * Q.residualSuffixEnvelope P w c u := by
  exact ProphetSecretary.Statistics.abs_prefixSum_le_twice_suffixEnvelope u (Q.transitionResidual P w c u)
    (π.stoppingTime r Finset.univ x u)

noncomputable def Instance.expectedResidualSuffixEnvelope (Q P : Instance n) (w c : ℝ) : ℝ :=
  ∫ u, Q.residualSuffixEnvelope P w c u ∂Instance.clocksLaw n

lemma Instance.expectedResidualSuffixEnvelope_nonnegative (Q P : Instance n) (w c : ℝ) :
    0 ≤ Q.expectedResidualSuffixEnvelope P w c :=
  integral_nonneg (fun _ => ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _)

/-- The signed residual of every admissible policy is controlled by the same
clock-only suffix envelope. This statement is pathwise in a future training outcome. -/
theorem RandomizedPolicy.abs_expectedReachedTransitionResidual_le_suffix (π : RandomizedPolicy n)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    |π.expectedReachedTransitionResidual Q P w c| ≤ 2 * Q.expectedResidualSuffixEnvelope P w c := by
  have hp : MeasurePreserving (fun ω : π.World => ω.2.1) (P.worldLaw π.seedLaw) (Instance.clocksLaw n) :=
    measurePreserving_fst.comp measurePreserving_snd
  have hE := Q.integrable_residualSuffixEnvelope P hQ hP hw hc
  have hEW := hp.integrable_comp_of_integrable hE
  have hR := π.rule.integrable_reachedTransitionResidual π.measurable_rule Q P hQ hP π.seedLaw hw hc
  have hmap := integral_map (μ := P.worldLaw π.seedLaw) hp.measurable.aemeasurable
    (Q.measurable_residualSuffixEnvelope P hQ hP hw hc).aestronglyMeasurable
  rw [hp.map_eq] at hmap
  change |∫ ω : π.World, π.rule.reachedTransitionResidual Q P w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw π.seedLaw| ≤ _
  calc
    _ ≤ ∫ ω : π.World, |π.rule.reachedTransitionResidual Q P w c ω.2.2 ω.1 ω.2.1| ∂P.worldLaw π.seedLaw :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω : π.World, 2 * Q.residualSuffixEnvelope P w c ω.2.1 ∂P.worldLaw π.seedLaw :=
      integral_mono hR.abs (hEW.const_mul 2)
        (fun ω => π.rule.abs_reachedTransitionResidual_le_suffix Q P w c ω.2.2 ω.1 ω.2.1)
    _ = 2 * Q.expectedResidualSuffixEnvelope P w c := by
      rw [integral_const_mul, ← hmap]
      rfl

/-- Actual cross-law value comparison from the two scalar optimizers and the
nonnegative action-loss term. No empirical unbiasedness is asserted here. -/
theorem Instance.abs_value_difference_le_residualSuffix (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    |optimalScalarValue Q w c - optimalScalarValue P w c| ≤
      2 * Q.expectedResidualSuffixEnvelope P w c := by
  let ρ := Q.valuePolicy hQ hw.le hc
  let π := P.valuePolicy hP hw.le hc
  have hρ := ρ.bellman_residualIdentity_split Q P hQ hP hw hc
  rw [Q.valuePolicy_expectedDesignActionLoss_zero P hQ hw hc, add_zero] at hρ
  have hρbound := abs_le.mp (ρ.abs_expectedReachedTransitionResidual_le_suffix Q P hQ hP hw hc)
  have hρopt := scalarObjective_le_optimal ρ P hP hw.le hc
  have hπ := π.bellman_residualIdentity_split Q P hQ hP hw hc
  have hπopt : π.scalarObjective P w c = optimalScalarValue P w c := P.valuePolicy_optimal hP hw hc
  rw [hπopt] at hπ
  have hπbound := abs_le.mp (π.abs_expectedReachedTransitionResidual_le_suffix Q P hQ hP hw hc)
  have hloss := π.expectedReachedDesignActionLoss_nonnegative Q P w c
  rw [abs_le]
  constructor <;> linarith

/-- The canonical design policy's true regret is at most four times the same
complete-path residual envelope. This is the finite comparison in `upstat:comparison`. -/
theorem Instance.valuePolicy_regret_le_residualSuffix (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue P w c - (Q.valuePolicy hQ hw.le hc).scalarObjective P w c ≤
      4 * Q.expectedResidualSuffixEnvelope P w c := by
  let ρ := Q.valuePolicy hQ hw.le hc
  have hρ := ρ.bellman_residualIdentity_split Q P hQ hP hw hc
  rw [Q.valuePolicy_expectedDesignActionLoss_zero P hQ hw hc, add_zero] at hρ
  have hρbound := abs_le.mp (ρ.abs_expectedReachedTransitionResidual_le_suffix Q P hQ hP hw hc)
  have hVbound := abs_le.mp (Q.abs_value_difference_le_residualSuffix P hQ hP hw hc)
  linarith

end ProphetSecretary.Model
