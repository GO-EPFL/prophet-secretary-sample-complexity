import ProphetSecretary.Model.SingleIdentity

/-!
# Extended nonnegative expectations

These definitions retain infinite nonnegative expectations. The real expectations in the
finite-mean theory remain unchanged; the comparison lemmas identify the two conventions
when the maximum is integrable.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.extendedExpectedMaximum (P : Instance n) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Instance.maximum x) ∂P.valuesLaw

noncomputable def Instance.extendedCoordinateMean (P : Instance n) (i : Fin n) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal x ∂P.law i

noncomputable def RandomizedPolicy.extendedExpectedReward (π : RandomizedPolicy n)
    (P : Instance n) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (π.realizedReward ω) ∂P.worldLaw π.seedLaw

lemma Instance.extendedCoordinateMean_eq (P : Instance n) (i : Fin n) :
    P.extendedCoordinateMean i = ∫⁻ x, ENNReal.ofReal (x i) ∂P.valuesLaw := by
  exact (measurePreserving_eval P.law i).lintegral_comp
    (measurable_id.ennreal_ofReal) |>.symm

lemma Instance.extendedExpectedMaximum_eq_of_integrable (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    P.extendedExpectedMaximum = ENNReal.ofReal P.expectedMaximum := by
  exact (ofReal_integral_eq_lintegral_ofReal hP
    (Filter.Eventually.of_forall Instance.maximum_nonnegative)).symm

lemma RandomizedPolicy.extendedExpectedReward_eq_of_integrable (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    π.extendedExpectedReward P = ENNReal.ofReal (π.expectedReward P) := by
  apply (ofReal_integral_eq_lintegral_ofReal (π.integrable_realizedReward P hP) _).symm
  have hv : MeasurePreserving (fun ω : π.World => ω.1)
      (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  filter_upwards [hv.quasiMeasurePreserving.ae P.ae_nonnegative] with ω hω
  exact π.rule.reward_nonnegative _ _ _ _ hω

lemma RandomizedPolicy.extendedExpectedReward_le_maximum (π : RandomizedPolicy n)
    (P : Instance n) : π.extendedExpectedReward P ≤ P.extendedExpectedMaximum := by
  have hv : MeasurePreserving (fun ω : π.World => ω.1)
      (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  calc
    _ ≤ ∫⁻ ω : π.World, ENNReal.ofReal (Instance.maximum ω.1)
        ∂P.worldLaw π.seedLaw :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (π.rule.reward_le_maximum _ _ _ _)
    _ = _ := hv.lintegral_comp Instance.measurable_maximum.ennreal_ofReal

lemma Instance.extendedExpectedMaximum_le_sum (P : Instance n) :
    P.extendedExpectedMaximum ≤ ∑ i, P.extendedCoordinateMean i := by
  calc
    _ ≤ ∫⁻ x, ∑ i, ENNReal.ofReal (x i) ∂P.valuesLaw := by
      apply lintegral_mono_ae
      filter_upwards [P.ae_nonnegative] with x hx
      exact (ENNReal.ofReal_le_ofReal (Instance.maximum_le_sum hx)).trans_eq
        (ENNReal.ofReal_sum_of_nonneg fun i _ => hx i)
    _ = ∑ i, ∫⁻ x, ENNReal.ofReal (x i) ∂P.valuesLaw := by
      exact lintegral_finsetSum _ (fun i _ => (measurable_pi_apply i).ennreal_ofReal)
    _ = _ := by simp_rw [← P.extendedCoordinateMean_eq]


lemma Instance.size_pos_of_extendedExpectedMaximum_eq_top (P : Instance n)
    (hP : P.extendedExpectedMaximum = ⊤) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  have hZero : P.extendedExpectedMaximum = 0 :=
    le_antisymm (by simpa using P.extendedExpectedMaximum_le_sum) bot_le
  rw [hZero] at hP
  exact ENNReal.zero_ne_top hP

end ProphetSecretary.Model
