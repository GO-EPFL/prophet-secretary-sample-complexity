import ProphetSecretary.Model.LateSelectionProbability

/-!
# Integrating a lower selection bound over a terminal window

The window length multiplies the conditional selection bound because the
candidate clock is an independent uniform. This follows from the constructed
fixed-time/value conditioning identity and actual Lebesgue integration.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Policy.selectionProbabilityAtTimeValue_abs_le_one (π : Policy Seed n)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) (t a : ℝ) :
    |π.selectionProbabilityAtTimeValue P ν i t a| ≤ 1 := by
  have hn := norm_integral_le_of_norm_le_const (μ := P.worldLaw ν)
    (f := fun ω => π.selectionIndicatorAtTimeValue i (ω,(t,a)))
    (Eventually.of_forall fun ω => by
      change ‖if _ then (1 : ℝ) else 0‖ ≤ 1
      split_ifs <;> norm_num)
  simpa only [Policy.selectionProbabilityAtTimeValue, Real.norm_eq_abs, probReal_univ, mul_one] using hn

/-- A local-in-time lower bound integrates to its window length, for any
admissible randomized policy. -/
theorem Policy.selectionProbabilityAtValue_ge_window (π : Policy Seed n)
    (hπ : π.IsMeasurable) (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (i : Fin n) (a : ℝ) {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hwindow : ∀ t ∈ Icc (1 - u) 1, r ≤ π.selectionProbabilityAtTimeValue P ν i t a) :
    u * r ≤ π.selectionProbabilityAtValue P ν i a := by
  let F : ℝ → ℝ := fun t => π.selectionProbabilityAtTimeValue P ν i t a
  have hpair : Measurable (fun z : World n Seed × ℝ => (z.1,(z.2,a))) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  have hG : Measurable (fun z : World n Seed × ℝ => π.selectionIndicatorAtTimeValue i (z.1,(z.2,a))) :=
    (π.measurable_selectionIndicatorAtTimeValue hπ i).comp hpair
  have hFm : Measurable F := hG.stronglyMeasurable.integral_prod_left'.measurable
  have hFI : Integrable F Instance.uniformClock := by
    apply Integrable.of_bound hFm.aestronglyMeasurable 1
    exact Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs] using π.selectionProbabilityAtTimeValue_abs_le_one P ν i t a
  let E : Set ℝ := Ici (1 - u)
  have hEI : Integrable (E.indicator (fun _ => r)) Instance.uniformClock :=
    (integrable_const r).indicator measurableSet_Ici
  have hclock : ∀ᵐ t ∂Instance.uniformClock, t ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have hpoint : (E.indicator (fun _ => r)) ≤ᵐ[Instance.uniformClock] F := by
    filter_upwards [hclock] with t ht
    by_cases hE : t ∈ E
    · rw [Set.indicator_of_mem hE]
      exact hwindow t ⟨hE, ht.2⟩
    · rw [Set.indicator_of_notMem hE]
      exact π.selectionProbabilityAtTimeValue_nonnegative P ν i t a
  have hmean := integral_mono_ae hEI hFI hpoint
  have hprob : Instance.uniformClock.real E = u := by
    simpa only [E, sub_sub_cancel] using
      (Instance.uniformClock_probability_ge (by linarith : 0 ≤ 1 - u) (by linarith : 1 - u ≤ 1))
  have hleft : (∫ t, E.indicator (fun _ => r) t ∂Instance.uniformClock) = u * r := by
    rw [integral_indicator_const r measurableSet_Ici, hprob, smul_eq_mul]
  rw [hleft] at hmean
  exact hmean.trans_eq (π.selectionProbabilityAtValue_eq_timeIntegral hπ P ν i a).symm

end ProphetSecretary.Model
