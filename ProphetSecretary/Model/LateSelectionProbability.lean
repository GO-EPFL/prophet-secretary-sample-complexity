import ProphetSecretary.Model.LateSelectionPathwise

/-!
# A lower bound at a fixed candidate time and value

Pending execution dominates canonical stopping. Markov's inequality controls
the other unseen first moment. A union bound joins these two events without
assuming independence between them; coordinate replacement has already been
constructed in the online model.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.canonical_selectionAtTimeValue_lower (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c a t : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (ha : 0 < a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hwait : c * (1 - t) ≤ w * a / 2) (i : Fin n) :
    let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
    (P.worldLaw (Measure.dirac ())).real {ω : World n Unit |
      t ≤ π.stoppingTime () Finset.univ ω.1 ω.2.1} - 2 * (1 - t) * P.totalFirstMoment / a ≤
      π.selectionProbabilityAtTimeValue P (Measure.dirac ()) i t a := by
  let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
  let μ := P.worldLaw (Measure.dirac ())
  let F : World n Unit → ℝ := fun ω => P.pendingFirstMoment i t ω.2.1
  let A : Set (World n Unit) := {ω | t ≤ π.stoppingTime () Finset.univ ω.1 ω.2.1}
  let B : Set (World n Unit) := {ω | a / 2 ≤ F ω}
  let C : Set (World n Unit) := {ω | π.ActualSelects () Finset.univ
    (Function.update ω.1 i a) (Function.update ω.2.1 i t) i}
  have hπ : π.IsMeasurable := P.valueThreshold_policy_isMeasurable hP hw.le hc
  have hC : MeasurableSet C := π.measurableSet_actualSelects hπ measurable_const
    (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i
  have hF : Measurable F := (P.measurable_pendingFirstMoment i t).comp
    (measurable_fst.comp measurable_snd)
  have hp := P.world_clocks_measurePreserving (Measure.dirac ())
  have hFI : Integrable F μ := hp.integrable_comp_of_integrable (P.integrable_pendingFirstMoment i t)
  have hi := integral_map (μ := μ) hp.measurable.aemeasurable
    (P.measurable_pendingFirstMoment i t).aestronglyMeasurable
  rw [hp.map_eq] at hi
  have hmean : (∫ ω, F ω ∂μ) ≤ (1 - t) * P.totalFirstMoment := by
    exact hi.symm.trans_le (P.integral_pendingFirstMoment_le i ht0 ht1)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := F) (Eventually.of_forall fun ω => P.pendingFirstMoment_nonnegative i t ω.2.1) hFI (a / 2)
  have hbad : μ.real B ≤ 2 * (1 - t) * P.totalFirstMoment / a := by
    change a / 2 * μ.real B ≤ _ at hm
    apply (le_div_iff₀ ha).mpr
    nlinarith only [hm, hmean]
  have hsub : ∀ᵐ ω ∂μ, ω ∈ A → ω ∈ C ∪ B := by
    filter_upwards [P.world_updated_clocks_distinct_ae (Measure.dirac ()) i t] with ω hu
    intro hA
    by_cases hB : ω ∈ B
    · exact Or.inr hB
    · have hsmall : F ω ≤ a / 2 := (not_le.mp hB).le
      have hr : t ≤ π.pendingTime () ω.1 ω.2.1 i :=
        hA.trans (thresholdPolicy.stoppingTime_le_pendingTime _
          (P.valueThreshold_monotone hP hw hc) () ω.1 ω.2.1 i)
      exact Or.inl (P.canonical_selects_of_pending_smallMean hP hw hc ht1 ω.1 ω.2.1 i hu hr hsmall hwait)
  have hunion : μ.real A ≤ μ.real C + μ.real B :=
    (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)).trans (measureReal_union_le C B)
  have heq : π.selectionProbabilityAtTimeValue P (Measure.dirac ()) i t a = μ.real C := by
    have hfun : (fun ω : World n Unit => π.selectionIndicatorAtTimeValue i (ω,(t,a))) =
        fun ω => if ω ∈ C then (1 : ℝ) else 0 := by
      funext ω
      rcases ω with ⟨x,u,r⟩
      cases r
      rfl
    change (∫ ω : World n Unit, π.selectionIndicatorAtTimeValue i (ω,(t,a)) ∂μ) = _
    rw [hfun]
    simpa only [Set.indicator_apply, Pi.one_apply] using (integral_indicator_one (μ := μ) hC)
  change μ.real A - _ ≤ _
  rw [heq]
  linarith only [hunion, hbad]

end ProphetSecretary.Model
