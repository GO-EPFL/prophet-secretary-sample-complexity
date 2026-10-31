import ProphetSecretary.Model.ClockConditionalReach
import ProphetSecretary.Probability.CandidateValue
import ProphetSecretary.Reach.RareReach

/-!
# Integrating the value of a reached candidate

For every admissible policy, the candidate's value can be resampled without
changing reach. The proof uses the actual replacement measure-preserving map
and the constructed causal reach invariance. This yields a leave-one-coordinate
integration identity; no reach/value independence is an interface premise.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Policy.integrable_clockReach_weight (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) {B : ℝ}
    (hbound : ∀ u, |F u| ≤ B) :
    Integrable (fun u => π.clockConditionalReach P ν u i * F u) (Instance.clocksLaw n) := by
  apply Integrable.of_bound ((π.measurable_clockConditionalReach hπ P ν i).mul hF).aestronglyMeasurable B
  exact Eventually.of_forall fun u => by
    change ‖π.clockConditionalReach P ν u i * F u‖ ≤ B
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (π.clockConditionalReach_nonnegative P ν u i)]
    have h := mul_le_mul (π.clockConditionalReach_le_one P ν u i) (hbound u)
      (abs_nonneg (F u)) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using h

theorem Policy.integral_reached_clockFunction (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ u, |F u| ≤ B) :
    (∫ ω : World n Seed, if π.Reaches ω.2.2 ω.1 ω.2.1 i then F ω.2.1 else 0 ∂P.worldLaw ν) =
      ∫ u, π.clockConditionalReach P ν u i * F u ∂Instance.clocksLaw n := by
  let L : World n Seed → ℝ := fun ω => if π.Reaches ω.2.2 ω.1 ω.2.1 i then F ω.2.1 else 0
  have hR : MeasurableSet {ω : World n Seed | π.Reaches ω.2.2 ω.1 ω.2.1 i} :=
    π.measurableSet_reaches hπ (measurable_snd.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hL : Measurable L := Measurable.ite hR
    (hF.comp (measurable_fst.comp measurable_snd)) measurable_const
  have hLI : Integrable L (P.worldLaw ν) := by
    apply Integrable.of_bound hL.aestronglyMeasurable B
    exact Eventually.of_forall fun ω => by
      dsimp [L]
      split_ifs
      · simpa only [Real.norm_eq_abs] using hbound ω.2.1
      · simpa using hB
  have hmap := P.clockFirstWorld_measurePreserving ν
  have hI : Integrable (fun z : (Fin n → ℝ) × ((Fin n → ℝ) × Seed) =>
      if π.Reaches z.2.2 z.2.1 z.1 i then F z.1 else 0)
      ((Instance.clocksLaw n).prod (P.valuesLaw.prod ν)) := hmap.integrable_comp_of_integrable hLI
  have heq := integral_map (μ := (Instance.clocksLaw n).prod (P.valuesLaw.prod ν))
    hmap.measurable.aemeasurable hL.aestronglyMeasurable
  rw [hmap.map_eq] at heq
  calc
    _ = ∫ z : (Fin n → ℝ) × ((Fin n → ℝ) × Seed),
        (if π.Reaches z.2.2 z.2.1 z.1 i then F z.1 else 0)
          ∂(Instance.clocksLaw n).prod (P.valuesLaw.prod ν) := heq
    _ = ∫ u, (∫ z : (Fin n → ℝ) × Seed, if π.Reaches z.2 z.1 u i then F u else 0
          ∂P.valuesLaw.prod ν) ∂Instance.clocksLaw n := integral_prod _ hI
    _ = _ := integral_congr_ae (Eventually.of_forall fun u => π.integral_clockReach_indicator hπ P ν u i (F u))

/-- The candidate-value integral is conditional only on the complete clock
vector. Reach coefficients average offers and the independent policy seed. -/
theorem Policy.integral_reached_offerFunction (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n)
    (Φ : (Fin n → ℝ) × ℝ → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ u a, |Φ (u, a)| ≤ B) :
    (∫ ω : World n Seed, if π.Reaches ω.2.2 ω.1 ω.2.1 i then Φ (ω.2.1, ω.1 i) else 0
      ∂P.worldLaw ν) =
      ∫ u, π.clockConditionalReach P ν u i * (∫ a, Φ (u, a) ∂P.law i) ∂Instance.clocksLaw n := by
  let L : World n Seed → ℝ := fun ω =>
    if π.Reaches ω.2.2 ω.1 ω.2.1 i then Φ (ω.2.1, ω.1 i) else 0
  let F : World n Seed × ℝ → ℝ := fun z =>
    if π.Reaches z.1.2.2 z.1.1 z.1.2.1 i then Φ (z.1.2.1, z.2) else 0
  let mean : (Fin n → ℝ) → ℝ := fun u => ∫ a, Φ (u, a) ∂P.law i
  have hR : MeasurableSet {ω : World n Seed | π.Reaches ω.2.2 ω.1 ω.2.1 i} :=
    π.measurableSet_reaches hπ (measurable_snd.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hL : Measurable L := Measurable.ite hR
    (hΦ.comp ((measurable_fst.comp measurable_snd).prodMk ((measurable_pi_apply i).comp measurable_fst)))
    measurable_const
  have hF : Measurable F := Measurable.ite (measurable_fst hR)
    (hΦ.comp (((measurable_fst.comp measurable_snd).comp measurable_fst).prodMk measurable_snd)) measurable_const
  have hLI : Integrable L (P.worldLaw ν) := by
    apply Integrable.of_bound hL.aestronglyMeasurable B
    exact Eventually.of_forall fun ω => by
      dsimp [L]
      split_ifs
      · simpa only [Real.norm_eq_abs] using hbound ω.2.1 (ω.1 i)
      · simpa using hB
  have hFI : Integrable F ((P.worldLaw ν).prod (P.law i)) := by
    apply Integrable.of_bound hF.aestronglyMeasurable B
    exact Eventually.of_forall fun z => by
      dsimp [F]
      split_ifs
      · simpa only [Real.norm_eq_abs] using hbound z.1.2.1 z.2
      · simpa using hB
  have hMean : Measurable mean := (hΦ.stronglyMeasurable.integral_prod_right' (ν := P.law i)).measurable
  have hMeanBound (u : Fin n → ℝ) : |mean u| ≤ B := by
    have h := norm_integral_le_of_norm_le_const (μ := P.law i) (f := fun a => Φ (u, a))
      (Eventually.of_forall fun a => by simpa only [Real.norm_eq_abs] using hbound u a)
    simpa only [mean, Real.norm_eq_abs, probReal_univ, mul_one] using h
  have hrep := P.replaceValue_measurePreserving ν i
  have heq := integral_map (μ := (P.worldLaw ν).prod (P.law i)) hrep.measurable.aemeasurable hL.aestronglyMeasurable
  rw [hrep.map_eq] at heq
  have hclock : ∀ᵐ z : World n Seed × ℝ ∂(P.worldLaw ν).prod (P.law i), z.1.2.1 i ≤ 1 :=
    (measurePreserving_fst (μ := P.worldLaw ν) (ν := P.law i)).quasiMeasurePreserving.ae
      ((P.world_clocks_mem_unitInterval ν).mono fun ω hω => (hω i).2)
  have hreplace : (∫ ω, L ω ∂P.worldLaw ν) = ∫ z, F z ∂(P.worldLaw ν).prod (P.law i) := by
    rw [heq]
    apply integral_congr_ae
    filter_upwards [hclock] with z hz
    change (if π.Reaches z.1.2.2 (Function.update z.1.1 i z.2) z.1.2.1 i then
      Φ (z.1.2.1, (Function.update z.1.1 i z.2) i) else 0) = F z
    rw [Function.update_self, π.reaches_update_value _ _ _ i z.2 hz]
  calc
    _ = ∫ z, F z ∂(P.worldLaw ν).prod (P.law i) := hreplace
    _ = ∫ ω : World n Seed, (∫ a, F (ω, a) ∂P.law i) ∂P.worldLaw ν := integral_prod _ hFI
    _ = ∫ ω : World n Seed, if π.Reaches ω.2.2 ω.1 ω.2.1 i then mean ω.2.1 else 0 ∂P.worldLaw ν := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by
        by_cases hr : π.Reaches ω.2.2 ω.1 ω.2.1 i
        · simp only [F, if_pos hr, mean]
        · simp only [F, if_neg hr, integral_zero]
    _ = _ := π.integral_reached_clockFunction hπ P ν i mean hMean hB hMeanBound

end ProphetSecretary.Model
