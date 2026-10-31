import ProphetSecretary.Model.LawThresholdVariation
import ProphetSecretary.Model.ScalarBands

/-!
# Finite quadratic policy regret under a likelihood-law change

The old canonical observer is evaluated under the new online law. Actual
clock anti-concentration controls each action loss, and the complete Bellman
performance identity sums the reached losses over all finite identities.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

noncomputable def Instance.lawLocalLoss (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) (ω : World n Unit) : ℝ :=
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  (Q.valuePolicy hQ hw.le hc).rule.arrivalBellmanLoss T w c () ω.1 ω.2.1 i

lemma Instance.lawLocalLoss_nonnegative (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) (ω : World n Unit) : 0 ≤ P.lawLocalLoss hw hc hbound h hh hb hm θ ρ i ω :=
  Policy.arrivalBellmanLoss_nonnegative _ _ _ _ _ _ _ _

lemma Instance.measurable_lawLocalLoss (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) : Measurable (P.lawLocalLoss hw hc hbound h hh hb hm θ ρ i) := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  have hT := T.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm ρ hbound)
  exact (Q.valuePolicy hQ hw.le hc).rule.measurable_arrivalBellmanLoss
    (Q.valuePolicy hQ hw.le hc).measurable_rule T hT hw hc measurable_const
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i

lemma Instance.integrable_lawLocalLoss (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (i : Fin n) :
    Integrable (P.lawLocalLoss hw hc hbound h hh hb hm θ ρ i)
      ((P.likelihoodWidePath h hh hb hm ρ).worldLaw (Measure.dirac ())) := by
  let D := (2 * (w * H + c) * (n : ℝ)) * |ρ - θ|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply Integrable.of_bound (P.measurable_lawLocalLoss hw hc hbound h hh hb hm θ ρ i).aestronglyMeasurable D
  filter_upwards [(P.likelihoodWidePath h hh hb hm ρ).world_clocks_mem_unitInterval (Measure.dirac ())] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (P.lawLocalLoss_nonnegative hw hc hbound h hh hb hm θ ρ i ω)]
  have hbnd := P.lawPolicy_localLoss_le_band hw hc hH hbound h hh hb hm hθ hρ ω.1 ω.2.1 i (hω i).1
  change P.lawLocalLoss hw hc hbound h hh hb hm θ ρ i ω ≤ if _ then D else 0 at hbnd
  split_ifs at hbnd
  · exact hbnd
  · exact hbnd.trans hD

/-- Quadratic regret from one independent candidate clock. -/
theorem Instance.expected_lawLocalLoss_le (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (i : Fin n) :
    (∫ ω : World n Unit, P.lawLocalLoss hw hc.le hbound h hh hb hm θ ρ i ω
      ∂(P.likelihoodWidePath h hh hb hm ρ).worldLaw (Measure.dirac ())) ≤
      8 * (1 + (n : ℝ)) * (2 * (w * H + c) * (n : ℝ)) ^ 2 * (ρ - θ) ^ 2 / c := by
  let T := P.likelihoodWidePath h hh hb hm ρ
  let μ := T.worldLaw (Measure.dirac ())
  have hT := T.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm ρ hbound)
  let D := (2 * (w * H + c) * (n : ℝ)) * |ρ - θ|
  let E : Set (World n Unit) := {ω | |w * ω.1 i - T.continuationAtArrival w c ω.1 ω.2.1 i| ≤ D}
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hv : Measurable (fun ω : World n Unit ↦ T.continuationAtArrival w c ω.1 ω.2.1 i) :=
    T.measurable_continuationAtArrival hT hw hc.le
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hE : MeasurableSet E := measurableSet_le (continuous_abs.measurable.comp
    ((measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).sub hv)) measurable_const
  have hp : ∀ᵐ ω : World n Unit ∂μ,
      P.lawLocalLoss hw hc.le hbound h hh hb hm θ ρ i ω ≤ E.indicator (fun _ ↦ D) ω := by
    filter_upwards [T.world_clocks_mem_unitInterval (Measure.dirac ())] with ω hω
    have hbnd := P.lawPolicy_localLoss_le_band hw hc.le hH hbound h hh hb hm hθ hρ ω.1 ω.2.1 i (hω i).1
    change P.lawLocalLoss hw hc.le hbound h hh hb hm θ ρ i ω ≤
      if |w * ω.1 i - T.continuationAtArrival w c ω.1 ω.2.1 i| ≤ D then D else 0 at hbnd
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem (s := E) he]
      have he' : |w * ω.1 i - T.continuationAtArrival w c ω.1 ω.2.1 i| ≤ D := he
      simpa only [if_pos he'] using hbnd
    · rw [Set.indicator_of_notMem (s := E) he]
      have hne : ¬ |w * ω.1 i - T.continuationAtArrival w c ω.1 ω.2.1 i| ≤ D := he
      simpa only [if_neg hne] using hbnd
  have hi := integral_mono_ae (P.integrable_lawLocalLoss hw hc.le hH hbound h hh hb hm hθ hρ i)
    ((integrable_const D).indicator hE) hp
  rw [integral_indicator_const _ hE, smul_eq_mul] at hi
  have hprob := T.acceptanceBand_probability hT (Measure.dirac ()) hw hc hD i
  calc
    _ ≤ μ.real E * D := hi
    _ ≤ (2 * D / (c / (4 * (1 + (n : ℝ))))) * D := mul_le_mul_of_nonneg_right hprob hD
    _ = _ := by
      dsimp only [D]
      rw [← sq_abs (ρ - θ)]
      field_simp [hc.ne', (show (4 : ℝ) * (1 + (n : ℝ)) ≠ 0 by positivity)]
      ring

noncomputable def finiteLawRegretConstant (n : ℕ) (H w c : ℝ) : ℝ :=
  8 * (n : ℝ) * (1 + (n : ℝ)) * (2 * (w * H + c) * (n : ℝ)) ^ 2 / c

/-- Full finite law-adaptation regret of the old canonical policy under the new
law. Every hypothesis describes the actual product instance and likelihood path. -/
theorem Instance.lawPolicy_regret_le (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    let Q := P.likelihoodWidePath h hh hb hm θ
    let T := P.likelihoodWidePath h hh hb hm ρ
    let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
    optimalScalarValue T w c - (Q.valuePolicy hQ hw.le hc.le).scalarObjective T w c ≤
      finiteLawRegretConstant n H w c * (ρ - θ) ^ 2 := by
  dsimp only
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  have hT := T.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm ρ hbound)
  let C := Q.valuePolicy hQ hw.le hc.le
  change optimalScalarValue T w c - C.scalarObjective T w c ≤ _
  rw [C.bellman_performanceDifference T hT hw hc.le]
  change (∫ ω : World n Unit, C.rule.reachedBellmanLoss T w c ω.2.2 ω.1 ω.2.1 ∂T.worldLaw (Measure.dirac ())) ≤ _
  have hpoint (ω : World n Unit) : C.rule.reachedBellmanLoss T w c ω.2.2 ω.1 ω.2.1 ≤
      ∑ i : Fin n, P.lawLocalLoss hw hc.le hbound h hh hb hm θ ρ i ω := by
    unfold Policy.reachedBellmanLoss
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact le_rfl
    · exact P.lawLocalLoss_nonnegative hw hc.le hbound h hh hb hm θ ρ i ω
  have hi := integral_mono
    (C.rule.integrable_reachedBellmanLoss C.measurable_rule T hT C.seedLaw hw hc.le)
    (integrable_finsetSum _ (fun i _ ↦ P.integrable_lawLocalLoss hw hc.le hH hbound h hh hb hm hθ hρ i)) hpoint
  change (∫ ω : World n Unit, C.rule.reachedBellmanLoss T w c ω.2.2 ω.1 ω.2.1 ∂T.worldLaw (Measure.dirac ())) ≤
    (∫ ω : World n Unit, ∑ i : Fin n, P.lawLocalLoss hw hc.le hbound h hh hb hm θ ρ i ω ∂T.worldLaw (Measure.dirac ())) at hi
  rw [integral_finsetSum Finset.univ (fun i _ ↦ P.integrable_lawLocalLoss hw hc.le hH hbound h hh hb hm hθ hρ i)] at hi
  calc
    _ ≤ ∑ i : Fin n, ∫ ω : World n Unit, P.lawLocalLoss hw hc.le hbound h hh hb hm θ ρ i ω ∂T.worldLaw (Measure.dirac ()) := hi
    _ ≤ ∑ _i : Fin n, 8 * (1 + (n : ℝ)) * (2 * (w * H + c) * (n : ℝ)) ^ 2 * (ρ - θ) ^ 2 / c :=
      Finset.sum_le_sum (fun i _ ↦ P.expected_lawLocalLoss_le hw hc hH hbound h hh hb hm hθ hρ i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold finiteLawRegretConstant
      ring

end ProphetSecretary.Model
