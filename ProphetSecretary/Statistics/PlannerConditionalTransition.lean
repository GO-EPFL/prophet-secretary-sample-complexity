import ProphetSecretary.Probability.UniformMaximum
import ProphetSecretary.Probability.BernoulliSubset

/-!
# The conditional seed law of the direct planner sampler

Given a nonempty subset `D` and a chosen identity `i`, independent uniform
vectors produce the maximum remaining-time fraction and all additional
Bernoulli inclusions. The expectation formula is derived for this concrete
product-seed execution.
-/

open MeasureTheory Set
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def plannerTailSet {n : ℕ} (A D : Finset (Fin n)) (i : Fin n)
    (s : ℝ) (u : Fin n → ℝ) : Finset (Fin n) :=
  D.erase i ∪ bernoulliSubset (A \ D) (fun _ => s) u

lemma measurable_plannerTailSet {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (A D : Finset (Fin n)) (i : Fin n) (s : Ω → ℝ) (u : Ω → Fin n → ℝ)
    (hs : Measurable s) (hu : ∀ j, Measurable (fun ω => u ω j)) :
    Measurable (fun ω => plannerTailSet A D i (s ω) (u ω)) := by
  rw [measurable_finset_iff]
  intro j
  have h := measurable_finset_iff.mp
    (measurable_bernoulliSubset (A \ D) (fun ω _ => s ω) u (fun _ => hs) hu) j
  simpa only [plannerTailSet, Finset.mem_union] using measurable_const.or h

noncomputable def plannerConditionalTransition {n : ℕ} (A D : Finset (Fin n))
    (hD : D.Nonempty) (i : Fin n)
    (u : (Fin D.card → ℝ) × (Fin n → ℝ)) : Fin n × ℝ × Finset (Fin n) :=
  let s := uniformMaximum D.card (Nat.succ_le_of_lt (Finset.card_pos.mpr hD)) u.1
  (i, s, plannerTailSet A D i s u.2)

lemma measurable_plannerConditionalTransition {n : ℕ} (A D : Finset (Fin n))
    (hD : D.Nonempty) (i : Fin n) : Measurable (plannerConditionalTransition A D hD i) := by
  have hmax : Measurable (fun a : (Fin D.card → ℝ) × (Fin n → ℝ) =>
      uniformMaximum D.card (Nat.succ_le_of_lt (Finset.card_pos.mpr hD)) a.1) :=
    (measurable_uniformMaximum D.card
      (Nat.succ_le_of_lt (Finset.card_pos.mpr hD))).comp measurable_fst
  exact measurable_const.prodMk (hmax.prodMk
    (measurable_plannerTailSet A D i _ _ hmax
      (fun j => (measurable_pi_apply j).comp measurable_snd)))

/-- Actual transition law using separate uniform vectors for the maximum
and the independent tail inclusions. -/
noncomputable def plannerConditionalTransitionLaw {n : ℕ} (A D : Finset (Fin n))
    (hD : D.Nonempty) (i : Fin n) : Measure (Fin n × ℝ × Finset (Fin n)) :=
  ((Instance.clocksLaw D.card).prod (Instance.clocksLaw n)).map
    (plannerConditionalTransition A D hD i)

instance plannerConditionalTransitionLaw_probability {n : ℕ} (A D : Finset (Fin n))
    (hD : D.Nonempty) (i : Fin n) :
    IsProbabilityMeasure (plannerConditionalTransitionLaw A D hD i) :=
  Measure.isProbabilityMeasure_map (measurable_plannerConditionalTransition A D hD i).aemeasurable

lemma lintegral_plannerConditionalTransitionLaw {n : ℕ} (A D : Finset (Fin n))
    (hD : D.Nonempty) (i : Fin n) (f : Fin n × ℝ × Finset (Fin n) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x, f x ∂plannerConditionalTransitionLaw A D hD i) =
      ∫⁻ s, ENNReal.ofReal ((D.card : ℝ) * s ^ (D.card - 1)) *
        ∑ T ∈ (A \ D).powerset,
          ENNReal.ofReal (s ^ T.card * (1 - s) ^ ((A \ D).card - T.card)) *
            f (i, s, D.erase i ∪ T) ∂Instance.uniformClock := by
  let G : ℝ → ℝ≥0∞ := fun s => ∑ T ∈ (A \ D).powerset,
    ENNReal.ofReal (s ^ T.card * (1 - s) ^ ((A \ D).card - T.card)) * f (i, s, D.erase i ∪ T)
  have hG : Measurable G := by
    apply Finset.measurable_sum
    intro T _
    exact (by fun_prop : Measurable (fun s : ℝ =>
      ENNReal.ofReal (s ^ T.card * (1 - s) ^ ((A \ D).card - T.card)))).mul
        (hf.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  rw [plannerConditionalTransitionLaw,
    lintegral_map hf (measurable_plannerConditionalTransition A D hD i)]
  change (∫⁻ a, (f ∘ plannerConditionalTransition A D hD i) a
    ∂(Instance.clocksLaw D.card).prod (Instance.clocksLaw n)) = _
  rw [lintegral_prod _ (hf.comp (measurable_plannerConditionalTransition A D hD i)).aemeasurable]
  have hm : 1 ≤ D.card := Nat.succ_le_of_lt (Finset.card_pos.mpr hD)
  calc
    (∫⁻ a, ∫⁻ u, f (plannerConditionalTransition A D hD i (a, u))
        ∂Instance.clocksLaw n ∂Instance.clocksLaw D.card) =
      ∫⁻ a, G (uniformMaximum D.card hm a) ∂Instance.clocksLaw D.card := by
      apply lintegral_congr_ae
      filter_upwards [uniformMaximum_mem_unit D.card hm] with a ha
      exact lintegral_bernoulliSubset_constant (A \ D) ha
        (fun T => f (i, uniformMaximum D.card hm a, D.erase i ∪ T))
    _ = _ := lintegral_uniformMaximum D.card hm G hG

end ProphetSecretary.Statistics
