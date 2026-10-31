import ProphetSecretary.Probability.FiniteClockCompensator

/-!
# Real finite-clock compensation with integrability

A bounded nonnegative premium gives an integrable arrival contribution and an
integrable stopped hazard on the world-time product. Equality of their real
expectations follows from the constructed nonnegative compensation identity.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Probability

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def realClockReachedPremium (π : Model.Policy Seed n) (i : Fin n)
    (g : ℝ × Model.World n Seed → ℝ) (ω : Model.World n Seed) : ℝ :=
  if π.Reaches ω.2.2 ω.1 ω.2.1 i then g (ω.2.1 i, Model.Instance.eraseClock i ω) else 0

noncomputable def realClockStoppedHazard (π : Model.Policy Seed n) (i : Fin n)
    (g : ℝ × Model.World n Seed → ℝ) (q : Model.World n Seed × ℝ) : ℝ :=
  if q.2 ≤ π.stoppingTime q.1.2.2 Finset.univ q.1.1 q.1.2.1 ∧ q.2 < q.1.2.1 i
    then g (q.2, Model.Instance.eraseClock i q.1) / (1 - q.2) else 0

lemma finite_clock_compensator_real (π : Model.Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n)
    (P : Model.Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : ℝ × Model.World n Seed → ℝ) (hg : Measurable g) (hgnn : ∀ q, 0 ≤ g q)
    {B : ℝ} (hbound : ∀ q, g q ≤ B) :
    Integrable (realClockReachedPremium π i g) (P.worldLaw ν) ∧
      Integrable (realClockStoppedHazard π i g) ((P.worldLaw ν).prod Model.Instance.uniformClock) ∧
      (∫ ω, realClockReachedPremium π i g ω ∂P.worldLaw ν) =
        ∫ ω, ∫ t, realClockStoppedHazard π i g (ω, t) ∂Model.Instance.uniformClock ∂P.worldLaw ν := by
  let G : ℝ × Model.World n Seed → ℝ≥0∞ := fun q => ENNReal.ofReal (g q)
  let R := clockReachedPremium π i G
  let H := clockStoppedHazard π i G
  have hG : Measurable G := hg.ennreal_ofReal
  have hR : Measurable R := measurable_clockReachedPremium π hπ i G hG
  have hH : Measurable H := measurable_clockStoppedHazard π hπ i G hG
  have hRfinite (ω : Model.World n Seed) : R ω < ∞ := by
    dsimp only [R, clockReachedPremium, G]
    split_ifs <;> simp
  have hRbound : (∫⁻ ω, R ω ∂P.worldLaw ν) < ∞ := by
    calc
      _ ≤ ∫⁻ _ω : Model.World n Seed, ENNReal.ofReal B ∂P.worldLaw ν := by
        apply lintegral_mono
        intro ω
        dsimp only [R, clockReachedPremium, G]
        split_ifs
        · exact ENNReal.ofReal_le_ofReal (hbound _)
        · exact zero_le
      _ < ∞ := by simp
  have hcomp := finite_clock_compensator π hπ i P ν G hG
  have hHbound : (∫⁻ q, H q ∂(P.worldLaw ν).prod Model.Instance.uniformClock) < ∞ := by
    rw [lintegral_prod _ hH.aemeasurable, ← hcomp]
    exact hRbound
  have hRtoReal (ω : Model.World n Seed) : (R ω).toReal = realClockReachedPremium π i g ω := by
    dsimp only [R, clockReachedPremium, G, realClockReachedPremium]
    split_ifs
    · exact ENNReal.toReal_ofReal (hgnn _)
    · rfl
  have hHtoReal : (fun q => (H q).toReal) =ᵐ[(P.worldLaw ν).prod Model.Instance.uniformClock]
      realClockStoppedHazard π i g := by
    have ht := (measurePreserving_snd (μ := P.worldLaw ν) (ν := Model.Instance.uniformClock)).quasiMeasurePreserving.ae
      uniformClock_mem_open_unit
    filter_upwards [ht] with q hq
    dsimp only [H, clockStoppedHazard, G, realClockStoppedHazard]
    split_ifs
    · rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (hgnn _), ENNReal.toReal_ofReal (sub_pos.mpr hq.2).le]
    · rfl
  have hRi : Integrable (realClockReachedPremium π i g) (P.worldLaw ν) := by
    exact (integrable_toReal_of_lintegral_ne_top hR.aemeasurable hRbound.ne).congr
      (Filter.Eventually.of_forall hRtoReal)
  have hHi : Integrable (realClockStoppedHazard π i g) ((P.worldLaw ν).prod Model.Instance.uniformClock) :=
    (integrable_toReal_of_lintegral_ne_top hH.aemeasurable hHbound.ne).congr hHtoReal
  refine ⟨hRi, hHi, ?_⟩
  calc
    _ = (∫⁻ ω, R ω ∂P.worldLaw ν).toReal := by
      rw [← integral_toReal hR.aemeasurable (Filter.Eventually.of_forall hRfinite)]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => (hRtoReal ω).symm))
    _ = (∫⁻ q, H q ∂(P.worldLaw ν).prod Model.Instance.uniformClock).toReal := by
      congr 1
      rw [lintegral_prod _ hH.aemeasurable]
      exact hcomp
    _ = ∫ q, (H q).toReal ∂(P.worldLaw ν).prod Model.Instance.uniformClock := by
      exact (integral_toReal hH.aemeasurable (ae_lt_top hH hHbound.ne)).symm
    _ = ∫ q, realClockStoppedHazard π i g q ∂(P.worldLaw ν).prod Model.Instance.uniformClock := integral_congr_ae hHtoReal
    _ = _ := integral_prod _ hHi

end ProphetSecretary.Probability
