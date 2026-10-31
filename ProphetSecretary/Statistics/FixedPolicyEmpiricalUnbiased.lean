import ProphetSecretary.Statistics.EmpiricalProductUnbiased
import ProphetSecretary.Model.ClippedOutcomeObservables

/-!
# Fixed-policy empirical evaluation is unbiased

Clipped reward and duration give a globally bounded measurable payoff kernel.
It agrees almost surely with the actual payoff under every cap-one instance.
Product-empirical unbiasedness therefore applies to every admissible randomized
policy fixed before the independent training samples are drawn.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal

namespace ProphetSecretary.Model
open ProphetSecretary.Probability

variable {n k : ℕ} [NeZero k]

namespace RandomizedPolicy

noncomputable def boundedScalarRealization (π : RandomizedPolicy n) (z : ℝ) (ω : π.World) : ℝ :=
  boundedOfferValue 1 (π.realizedReward ω)+z*boundedOfferValue 1 (π.realizedDuration ω)

lemma measurable_boundedScalarRealization (π : RandomizedPolicy n) (z : ℝ) :
    Measurable (π.boundedScalarRealization z) :=
  (((boundedOfferValue 1).continuous.measurable.comp π.measurable_realizedReward).add
    (((boundedOfferValue 1).continuous.measurable.comp π.measurable_realizedDuration).const_mul z))

lemma boundedScalarRealization_bound (π : RandomizedPolicy n) (z : ℝ) (ω : π.World) :
    ‖π.boundedScalarRealization z ω‖≤1 + |z| := by
  have hR := boundedOfferValue_mem_range (1 : ℝ≥0) (π.realizedReward ω)
  have hT := boundedOfferValue_mem_range (1 : ℝ≥0) (π.realizedDuration ω)
  have hRa : |boundedOfferValue 1 (π.realizedReward ω)| ≤ 1 := by rw [abs_of_nonneg hR.1]; exact hR.2
  have hTa : |boundedOfferValue 1 (π.realizedDuration ω)| ≤ 1 := by rw [abs_of_nonneg hT.1]; exact hT.2
  change |boundedOfferValue 1 (π.realizedReward ω)+z*boundedOfferValue 1 (π.realizedDuration ω)| ≤ _
  calc
    _ ≤ |boundedOfferValue 1 (π.realizedReward ω)| + |z*boundedOfferValue 1 (π.realizedDuration ω)| := abs_add_le _ _
    _ ≤ 1 + |z| * 1 := add_le_add hRa (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hTa (abs_nonneg z))
    _ = _ := by ring

noncomputable def boundedScalarKernel (π : RandomizedPolicy n) (z : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ ur, π.boundedScalarRealization z (x,ur) ∂(Instance.clocksLaw n).prod π.seedLaw

lemma measurable_boundedScalarKernel (π : RandomizedPolicy n) (z : ℝ) :
    Measurable (π.boundedScalarKernel z) :=
  ((π.measurable_boundedScalarRealization z).stronglyMeasurable.integral_prod_right').measurable

lemma boundedScalarKernel_bound (π : RandomizedPolicy n) (z : ℝ) (x : Fin n → ℝ) :
    ‖π.boundedScalarKernel z x‖≤1 + |z| := by
  simpa only [boundedScalarKernel,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=(Instance.clocksLaw n).prod π.seedLaw)
    (Eventually.of_forall fun ur => π.boundedScalarRealization_bound z (x,ur))

/-- The bounded kernel represents the actual scalar objective under every
cap-one instance, with the same independent seed and physical duration. -/
theorem scalarObjective_eq_boundedScalarKernel (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (z : ℝ) :
    π.scalarObjective P 1 z = ∫ x, π.boundedScalarKernel z x ∂P.valuesLaw := by
  have hI : Integrable (π.boundedScalarRealization z) (P.worldLaw π.seedLaw) :=
    Integrable.of_bound (π.measurable_boundedScalarRealization z).aestronglyMeasurable (1 + |z|)
      (Eventually.of_forall fun ω => π.boundedScalarRealization_bound z ω)
  have hvals : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i∈Icc (0:ℝ) 1 := by
    have hb := ae_all_iff.mpr fun i => (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hcap i)
    filter_upwards [P.ae_nonnegative,hb] with x hx hb
    exact fun i => ⟨hx i,hb i⟩
  have hv := (measurePreserving_fst (μ:=P.valuesLaw) (ν:=(Instance.clocksLaw n).prod π.seedLaw)).quasiMeasurePreserving.ae hvals
  have ht := ((measurePreserving_fst (μ:=Instance.clocksLaw n) (ν:=π.seedLaw)).comp
    (measurePreserving_snd (μ:=P.valuesLaw) (ν:=(Instance.clocksLaw n).prod π.seedLaw))).quasiMeasurePreserving.ae
      (Instance.clocks_mem_unitInterval (n:=n))
  have he : (fun ω : π.World => π.realizedReward ω+z*π.realizedDuration ω) =ᵐ[P.worldLaw π.seedLaw]
      π.boundedScalarRealization z := by
    filter_upwards [hv,ht] with ω hv ht
    have hr := π.rule.boundedRewardObservable_eq 1 ω.2.2 Finset.univ ω.1 ω.2.1 hv
    have hd := π.rule.boundedDurationObservable_eq ω.2.2 Finset.univ ω.1 ω.2.1 (fun i => (ht i).1)
    change _ = boundedOfferValue 1 (π.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1)+
      z*boundedOfferValue 1 (π.rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1)
    exact congrArg₂ (fun r d => r+z*d) hr.symm hd.symm
  change (∫ ω, 1*π.realizedReward ω+z*π.realizedDuration ω ∂P.worldLaw π.seedLaw) = _
  simp only [one_mul]
  rw [integral_congr_ae he]
  exact integral_prod _ hI

end RandomizedPolicy

theorem RandomizedPolicy.integrable_empiricalScalarObjective (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (z : ℝ) :
    Integrable (fun y : Reservoir n k => π.scalarObjective (totalEmpiricalInstance y) 1 z) (P.reservoirLaw k) := by
  have hI := P.integrable_empiricalProduct_bounded_fixed (k:=k) (π.measurable_boundedScalarKernel z) (π.boundedScalarKernel_bound z)
  have hb : ∀ᵐ y ∂P.reservoirLaw k, ∀ i l, y i l≤1 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun l =>
      (P.reservoir_coordinate_measurePreserving k i l).quasiMeasurePreserving.ae (hcap i)
  exact hI.congr (hb.mono fun y hy =>
    (π.scalarObjective_eq_boundedScalarKernel _ (totalEmpiricalInstance_bounded y zero_le_one hy) z).symm)

/-- Unbiasedness applies to a fixed policy and fixed scalar. It is not a
centering identity for a policy or scalar selected from the same samples. -/
theorem RandomizedPolicy.integral_empiricalScalarObjective (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (z : ℝ) :
    (∫ y : Reservoir n k, π.scalarObjective (totalEmpiricalInstance y) 1 z ∂P.reservoirLaw k) =
      π.scalarObjective P 1 z := by
  have hb : ∀ᵐ y ∂P.reservoirLaw k, ∀ i l, y i l≤1 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun l =>
      (P.reservoir_coordinate_measurePreserving k i l).quasiMeasurePreserving.ae (hcap i)
  calc
    _ = ∫ y, (∫ x, π.boundedScalarKernel z x ∂(totalEmpiricalInstance y).valuesLaw) ∂P.reservoirLaw k := by
      apply integral_congr_ae
      exact hb.mono fun y hy => π.scalarObjective_eq_boundedScalarKernel _
        (totalEmpiricalInstance_bounded y zero_le_one hy) z
    _ = ∫ x, π.boundedScalarKernel z x ∂P.valuesLaw :=
      P.integral_empiricalProduct_bounded_fixed (π.measurable_boundedScalarKernel z) (π.boundedScalarKernel_bound z)
    _ = _ := (π.scalarObjective_eq_boundedScalarKernel P hcap z).symm

end ProphetSecretary.Model
