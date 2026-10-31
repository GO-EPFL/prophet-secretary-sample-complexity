import ProphetSecretary.Model.MappedPremium
import ProphetSecretary.Probability.ReachedValueIntegration

/-!
# Reached premium cancellation for mapped rewards

The original offer vector determines observations and reach. The mapped law
determines rewards. Candidate resampling proves the cancellation against the
general-design residual without supplying any future observations to a policy.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Policy.integrable_reached_bounded (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n)
    (F : World n Seed → ℝ) (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ ω, |F ω| ≤ B) :
    Integrable (fun ω => if π.Reaches ω.2.2 ω.1 ω.2.1 i then F ω else 0) (P.worldLaw ν) := by
  have hr := π.measurableSet_reaches hπ (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  apply Integrable.of_bound (Measurable.ite hr hF measurable_const).aestronglyMeasurable B
  exact Eventually.of_forall fun ω => by
    split_ifs
    · simpa only [Real.norm_eq_abs] using hbound ω
    · simpa using hB

theorem Policy.integral_reached_mappedPremiumDifference (π : Policy Seed n) (hπ : π.IsMeasurable)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {h w c : ℝ}
    (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 ≤ c) (hdispl : ∀ i a, |f i a - a| ≤ h) (i : Fin n) :
    (∫ ω : World n Seed, if π.Reaches ω.2.2 ω.1 ω.2.1 i then
      Q.mappedPremiumDifference f w c i (ω.2.1, ω.1 i) else 0 ∂P.worldLaw ν) =
    ∫ ω : World n Seed, if π.Reaches ω.2.2 ω.1 ω.2.1 i then
      Q.transitionResidual (P.mapValues f hf hnn) w c ω.2.1 i - Q.transitionResidual P w c ω.2.1 i
      else 0 ∂P.worldLaw ν := by
  let Φ := Q.mappedPremiumDifference f w c i
  let mean : (Fin n → ℝ) → ℝ := fun u => ∫ a, Φ (u, a) ∂P.law i
  have hΦ : Measurable Φ := Q.measurable_mappedPremiumDifference hQ f hf hw hc i
  have hb : ∀ u a, |Φ (u, a)| ≤ w * h := Q.mappedPremiumDifference_bound f hw.le hdispl c i
  have hB : 0 ≤ w * h := mul_nonneg hw.le hh
  have hm : Measurable mean := (hΦ.stronglyMeasurable.integral_prod_right' (ν := P.law i)).measurable
  have hmb (u : Fin n → ℝ) : |mean u| ≤ w * h := by
    have hb' := norm_integral_le_of_norm_le_const (μ := P.law i) (f := fun a => Φ (u, a))
      (Eventually.of_forall fun a => by simpa only [Real.norm_eq_abs] using hb u a)
    simpa only [mean, Real.norm_eq_abs, probReal_univ, mul_one] using hb'
  have hMeanEq (u : Fin n → ℝ) : mean u =
      Q.transitionResidual (P.mapValues f hf hnn) w c u i - Q.transitionResidual P w c u i :=
    Q.integral_mappedPremiumDifference_general P hQ hP f hf hnn hdispl w c i u
  calc
    _ = ∫ u, π.clockConditionalReach P ν u i * mean u ∂Instance.clocksLaw n :=
      π.integral_reached_offerFunction hπ P ν i Φ hΦ hB hb
    _ = ∫ ω : World n Seed, if π.Reaches ω.2.2 ω.1 ω.2.1 i then mean ω.2.1 else 0 ∂P.worldLaw ν :=
      (π.integral_reached_clockFunction hπ P ν i mean hm hB hmb).symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun ω =>
      congrArg (fun v => if π.Reaches ω.2.2 ω.1 ω.2.1 i then v else 0) (hMeanEq ω.2.1))

/-- Summed cancellation with integrability of both reached sums made explicit. -/
theorem Policy.mappedPremium_residual_cancellation (π : Policy Seed n) (hπ : π.IsMeasurable)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {h w c : ℝ}
    (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 ≤ c) (hdispl : ∀ i a, |f i a - a| ≤ h) :
    Integrable (fun ω : World n Seed => π.reachedMaxDifference Q f w c ω.2.2 ω.1 ω.2.1) (P.worldLaw ν) ∧
    (∫ ω : World n Seed, π.reachedMaxDifference Q f w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw ν) =
      ∫ ω : World n Seed, π.reachedTransitionResidual Q (P.mapValues f hf hnn) w c ω.2.2 ω.1 ω.2.1 -
        π.reachedTransitionResidual Q P w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw ν := by
  let Φ := fun i => Q.mappedPremiumDifference f w c i
  let G := fun i (ω : World n Seed) => if π.Reaches ω.2.2 ω.1 ω.2.1 i then Φ i (ω.2.1, ω.1 i) else 0
  let R := fun i (ω : World n Seed) => if π.Reaches ω.2.2 ω.1 ω.2.1 i then
    Q.transitionResidual (P.mapValues f hf hnn) w c ω.2.1 i - Q.transitionResidual P w c ω.2.1 i else 0
  have hΦ (i : Fin n) : Measurable (Φ i) := Q.measurable_mappedPremiumDifference hQ f hf hw hc i
  have hB : 0 ≤ w * h := mul_nonneg hw.le hh
  have hG (i : Fin n) : Integrable (G i) (P.worldLaw ν) := by
    apply π.integrable_reached_bounded hπ P ν i _
      ((hΦ i).comp ((measurable_fst.comp measurable_snd).prodMk ((measurable_pi_apply i).comp measurable_fst))) hB
    intro ω
    exact Q.mappedPremiumDifference_bound f hw.le hdispl c i ω.2.1 (ω.1 i)
  have hMeanEq (i : Fin n) (u : Fin n → ℝ) : (∫ a, Φ i (u, a) ∂P.law i) =
      Q.transitionResidual (P.mapValues f hf hnn) w c u i - Q.transitionResidual P w c u i :=
    Q.integral_mappedPremiumDifference_general P hQ hP f hf hnn hdispl w c i u
  have hR (i : Fin n) : Integrable (R i) (P.worldLaw ν) := by
    let mean : (Fin n → ℝ) → ℝ := fun u => ∫ a, Φ i (u, a) ∂P.law i
    have hm : Measurable mean := ((hΦ i).stronglyMeasurable.integral_prod_right' (ν := P.law i)).measurable
    have hb (u : Fin n → ℝ) : |mean u| ≤ w * h := by
      have hb' := norm_integral_le_of_norm_le_const (μ := P.law i) (f := fun a => Φ i (u, a))
        (Eventually.of_forall fun a => by
          simpa only [Real.norm_eq_abs] using (Q.mappedPremiumDifference_bound f hw.le hdispl c i u a))
      simpa only [mean, Real.norm_eq_abs, probReal_univ, mul_one] using hb'
    have hi := π.integrable_reached_bounded hπ P ν i (fun ω => mean ω.2.1)
      (hm.comp (measurable_fst.comp measurable_snd)) hB (fun ω => hb ω.2.1)
    apply hi.congr
    exact Eventually.of_forall fun ω =>
      congrArg (fun v => if π.Reaches ω.2.2 ω.1 ω.2.1 i then v else 0) (hMeanEq i ω.2.1)
  have hrepr (ω : World n Seed) : π.reachedMaxDifference Q f w c ω.2.2 ω.1 ω.2.1 = ∑ i, G i ω := by
    unfold Policy.reachedMaxDifference
    apply Finset.sum_congr rfl
    intro i _
    dsimp [G, Φ, Instance.mappedPremiumDifference]
    rw [Q.continuationAtArrival_values_invariant w c ω.1 (fun _ => 0) ω.2.1 i]
  have hreprR (ω : World n Seed) : (∑ i, R i ω) =
      π.reachedTransitionResidual Q (P.mapValues f hf hnn) w c ω.2.2 ω.1 ω.2.1 -
        π.reachedTransitionResidual Q P w c ω.2.2 ω.1 ω.2.1 := by
    unfold Policy.reachedTransitionResidual
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [R]
    split_ifs <;> simp
  refine ⟨(integrable_finsetSum _ (fun i _ => hG i)).congr (Eventually.of_forall fun ω => (hrepr ω).symm), ?_⟩
  calc
    _ = ∫ ω, ∑ i, G i ω ∂P.worldLaw ν := integral_congr_ae (Eventually.of_forall hrepr)
    _ = ∑ i, ∫ ω, G i ω ∂P.worldLaw ν := integral_finsetSum _ (fun i _ => hG i)
    _ = ∑ i, ∫ ω, R i ω ∂P.worldLaw ν := Finset.sum_congr rfl (fun i _ =>
      π.integral_reached_mappedPremiumDifference hπ Q P hQ hP f hf hnn ν hh hw hc hdispl i)
    _ = ∫ ω, ∑ i, R i ω ∂P.worldLaw ν := (integral_finsetSum _ (fun i _ => hR i)).symm
    _ = _ := integral_congr_ae (Eventually.of_forall hreprR)

end ProphetSecretary.Model
