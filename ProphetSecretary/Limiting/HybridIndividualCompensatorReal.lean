import ProphetSecretary.Limiting.HybridIndividualCompensator

/-!
# Real individual-offer compensation in a hybrid process

A bounded nonnegative premium gives an integrable arrival contribution and an
integrable stopped hazard on the world-time product. Equality of their real
expectations follows from the constructed nonnegative compensation identity.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def HybridRule.realIndividualReachedPremium (π : HybridRule n Seed) (i : Fin n)
    (g : ℝ × HybridWorld n Seed → ℝ) (v : HybridWorld n Seed) : ℝ :=
  if v.2.2.1 i ≤ π.realizedDuration v then g (v.2.2.1 i, eraseIndividualClock i v) else 0

noncomputable def HybridRule.realIndividualStoppedHazard (π : HybridRule n Seed) (i : Fin n)
    (g : ℝ × HybridWorld n Seed → ℝ) (q : HybridWorld n Seed × ℝ) : ℝ :=
  if q.2 ≤ π.realizedDuration q.1 ∧ q.2 < q.1.2.2.1 i
    then g (q.2, eraseIndividualClock i q.1) / (1 - q.2) else 0

lemma HybridRule.individual_compensator_real (π : HybridRule n Seed) (hπ : π.IsMeasurable) (i : Fin n)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : ℝ × HybridWorld n Seed → ℝ) (hg : Measurable g) (hgnn : ∀ q, 0 ≤ g q)
    {B : ℝ} (hbound : ∀ q, g q ≤ B) :
    Integrable (HybridRule.realIndividualReachedPremium π i g) (hybridWorldLaw P μ ν) ∧
      Integrable (HybridRule.realIndividualStoppedHazard π i g) ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) ∧
      (∫ ω, HybridRule.realIndividualReachedPremium π i g ω ∂hybridWorldLaw P μ ν) =
        ∫ ω, ∫ t, HybridRule.realIndividualStoppedHazard π i g (ω, t) ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ ν := by
  let G : ℝ × HybridWorld n Seed → ℝ≥0∞ := fun q => ENNReal.ofReal (g q)
  let R := HybridRule.individualReachedPremium π i G
  let H := HybridRule.individualStoppedHazard π i G
  have hG : Measurable G := hg.ennreal_ofReal
  have hR : Measurable R := HybridRule.measurable_individualReachedPremium π hπ i G hG
  have hH : Measurable H := HybridRule.measurable_individualStoppedHazard π hπ i G hG
  have hRfinite (ω : HybridWorld n Seed) : R ω < ∞ := by
    dsimp only [R, HybridRule.individualReachedPremium, G]
    split_ifs <;> simp
  have hRbound : (∫⁻ ω, R ω ∂hybridWorldLaw P μ ν) < ∞ := by
    calc
      _ ≤ ∫⁻ _ω : HybridWorld n Seed, ENNReal.ofReal B ∂hybridWorldLaw P μ ν := by
        apply lintegral_mono
        intro ω
        dsimp only [R, HybridRule.individualReachedPremium, G]
        split_ifs
        · exact ENNReal.ofReal_le_ofReal (hbound _)
        · exact zero_le
      _ < ∞ := by simp
  have hcomp := π.individual_compensator hπ i P μ ν G hG
  have hHbound : (∫⁻ q, H q ∂(hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) < ∞ := by
    rw [lintegral_prod _ hH.aemeasurable, ← hcomp]
    exact hRbound
  have hRtoReal (ω : HybridWorld n Seed) : (R ω).toReal = HybridRule.realIndividualReachedPremium π i g ω := by
    dsimp only [R, HybridRule.individualReachedPremium, G, HybridRule.realIndividualReachedPremium]
    split_ifs
    · exact ENNReal.toReal_ofReal (hgnn _)
    · rfl
  have hHtoReal : (fun q => (H q).toReal) =ᵐ[(hybridWorldLaw P μ ν).prod Model.Instance.uniformClock]
      HybridRule.realIndividualStoppedHazard π i g := by
    have ht := (measurePreserving_snd (μ := hybridWorldLaw P μ ν) (ν := Model.Instance.uniformClock)).quasiMeasurePreserving.ae
      Probability.uniformClock_mem_open_unit
    filter_upwards [ht] with q hq
    dsimp only [H, HybridRule.individualStoppedHazard, G, HybridRule.realIndividualStoppedHazard]
    split_ifs
    · rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (hgnn _), ENNReal.toReal_ofReal (sub_pos.mpr hq.2).le]
    · rfl
  have hRi : Integrable (HybridRule.realIndividualReachedPremium π i g) (hybridWorldLaw P μ ν) := by
    exact (integrable_toReal_of_lintegral_ne_top hR.aemeasurable hRbound.ne).congr
      (Filter.Eventually.of_forall hRtoReal)
  have hHi : Integrable (HybridRule.realIndividualStoppedHazard π i g) ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) :=
    (integrable_toReal_of_lintegral_ne_top hH.aemeasurable hHbound.ne).congr hHtoReal
  refine ⟨hRi, hHi, ?_⟩
  calc
    _ = (∫⁻ ω, R ω ∂hybridWorldLaw P μ ν).toReal := by
      rw [← integral_toReal hR.aemeasurable (Filter.Eventually.of_forall hRfinite)]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => (hRtoReal ω).symm))
    _ = (∫⁻ q, H q ∂(hybridWorldLaw P μ ν).prod Model.Instance.uniformClock).toReal := by
      congr 1
      rw [lintegral_prod _ hH.aemeasurable]
      exact hcomp
    _ = ∫ q, (H q).toReal ∂(hybridWorldLaw P μ ν).prod Model.Instance.uniformClock := by
      exact (integral_toReal hH.aemeasurable (ae_lt_top hH hHbound.ne)).symm
    _ = ∫ q, HybridRule.realIndividualStoppedHazard π i g q ∂(hybridWorldLaw P μ ν).prod Model.Instance.uniformClock := integral_congr_ae hHtoReal
    _ = _ := integral_prod _ hHi

end ProphetSecretary.Limiting
