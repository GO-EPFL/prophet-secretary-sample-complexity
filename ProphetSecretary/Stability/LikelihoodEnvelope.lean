import ProphetSecretary.Stability.ScoreStability
import ProphetSecretary.Stability.SmallErrors
import ProphetSecretary.Probability.PolicyLikelihood
import ProphetSecretary.Analysis.StableEnvelope
import ProphetSecretary.Model.Scaling
import ProphetSecretary.Model.CanonicalNormalization

/-!
# Finite likelihood envelopes

The likelihood derivative first holds with a policy fixed. Coupled outcome
stability then controls this derivative for nearly optimal policies; the stable
envelope theorem separately differentiates the reoptimized value.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- The derivative of a fixed policy's scalar objective under a product likelihood
tilt. It uses the complete-vector score, regardless of the policy's stopping time. -/
noncomputable def RandomizedPolicy.scalarLikelihoodDerivative (π : RandomizedPolicy n)
    (P : Instance n) (w c : ℝ) (h : Fin n → ℝ → ℝ) : ℝ :=
  ∫ ω : π.World, (w * π.realizedReward ω + c * π.realizedDuration ω) *
    ProphetSecretary.Probability.completeScore h ω.1 ∂P.worldLaw π.seedLaw

lemma Instance.completeScore_bound_ae (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) :
    ∀ᵐ x ∂P.valuesLaw, |ProphetSecretary.Probability.completeScore h x| ≤ (n : ℝ) := by
  have hb' : ∀ᵐ x ∂P.valuesLaw, ∀ i, |h i (x i)| ≤ 1 := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hb i)
  filter_upwards [hb'] with x hx
  calc
    _ ≤ ∑ i : Fin n, |h i (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hx i
    _ = (n : ℝ) := by simp

/-- Erasing an independent seed preserves the law of the complete observed instance. -/
lemma Instance.eraseSeed_measurePreserving (P : Instance n) (π : RandomizedPolicy n) :
    MeasurePreserving (fun ω : π.World => (ω.1, (ω.2.1, ())))
      (P.worldLaw π.seedLaw) (P.worldLaw (Measure.dirac ())) := by
  have hs : MeasurePreserving (fun _ : π.Seed => ()) π.seedLaw (Measure.dirac ()) :=
    ⟨measurable_const, by simp [Measure.map_const]⟩
  exact (MeasurePreserving.id P.valuesLaw).prod
    ((MeasurePreserving.id (Instance.clocksLaw n)).prod hs)

lemma RandomizedPolicy.scalarLikelihoodDerivative_bound (π : RandomizedPolicy n) (P : Instance n)
    {H w c : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hw : 0 ≤ w) (hc : 0 ≤ c) (h : Fin n → ℝ → ℝ)
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) :
    |π.scalarLikelihoodDerivative P w c h| ≤ (w * H + c) * (n : ℝ) := by
  have hp : MeasurePreserving (fun ω : π.World => ω.1)
      (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  have hnorm := norm_integral_le_of_norm_le_const (μ := P.worldLaw π.seedLaw)
    (f := fun ω : π.World => (w * π.realizedReward ω + c * π.realizedDuration ω) *
      ProphetSecretary.Probability.completeScore h ω.1) (C := (w * H + c) * (n : ℝ)) (by
      filter_upwards [π.scalarPayoff_bound_ae P hH hbound hw hc,
        hp.quasiMeasurePreserving.ae (P.completeScore_bound_ae h hb)] with ω hω hZ
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hω hZ (abs_nonneg _) (by positivity))
  simpa only [scalarLikelihoodDerivative, Real.norm_eq_abs, probReal_univ, mul_one] using hnorm

/-- Fixed-policy derivative stability, with an explicit finite-dimensional bound.
The common cap/weights and the canonical optimizer are held at the base law. -/
lemma RandomizedPolicy.scalarLikelihoodDerivative_difference_le (π : RandomizedPolicy n)
    (P : Instance n) {H w c : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hw : 0 < w) (hc : 0 ≤ c) (hw1 : w ≤ 1) (hc1 : c ≤ 1)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) :
    |π.scalarLikelihoodDerivative P w c h -
      (P.valuePolicy (P.integrable_maximum_of_bounded hbound) hw.le hc).scalarLikelihoodDerivative P w c h| ≤
        (n : ℝ) * π.expectedOutcomeError P w c := by
  let π₀ := P.valuePolicy (P.integrable_maximum_of_bounded hbound) hw.le hc
  let Z : π.World → ℝ := fun ω => ProphetSecretary.Probability.completeScore h ω.1
  let F : ProphetSecretary.Model.World n Unit → ℝ := fun ω =>
    (w * (P.canonicalRule w c).reward () Finset.univ ω.1 ω.2.1 +
      c * (P.canonicalRule w c).stoppingTime () Finset.univ ω.1 ω.2.1) *
        ProphetSecretary.Probability.completeScore h ω.1
  have hmF : Measurable F :=
    ((measurable_const.mul π₀.measurable_realizedReward).add
      (measurable_const.mul π₀.measurable_realizedDuration)).mul
        ((ProphetSecretary.Probability.measurable_completeScore hh).comp measurable_fst)
  have hFint : Integrable F (P.worldLaw π₀.seedLaw) :=
    π₀.integrable_scalarScore_of_bounded P hH hbound hw.le hc h hh hb
  have hseed := P.eraseSeed_measurePreserving π
  have heq := integral_map (μ := P.worldLaw π.seedLaw) hseed.measurable.aemeasurable hmF.aestronglyMeasurable
  rw [hseed.map_eq] at heq
  have hπint := π.integrable_scalarScore_of_bounded P hH hbound hw.le hc h hh hb
  have hπ₀int := hseed.integrable_comp_of_integrable hFint
  have hsub : π.scalarLikelihoodDerivative P w c h - π₀.scalarLikelihoodDerivative P w c h =
      ∫ ω : π.World,
        ((w * π.realizedReward ω + c * π.realizedDuration ω) * Z ω -
          F (ω.1, (ω.2.1, ()))) ∂P.worldLaw π.seedLaw := by
    have hs := integral_sub hπint hπ₀int
    change (∫ ω : π.World,
        ((w * π.realizedReward ω + c * π.realizedDuration ω) * Z ω -
          F (ω.1, (ω.2.1, ()))) ∂P.worldLaw π.seedLaw) =
      π.scalarLikelihoodDerivative P w c h -
        (∫ ω : π.World, F (ω.1, (ω.2.1, ())) ∂P.worldLaw π.seedLaw) at hs
    rw [← heq] at hs
    exact hs.symm
  rw [hsub]
  have hp : MeasurePreserving (fun ω : π.World => ω.1)
      (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  have hnorm : ∀ᵐ ω : π.World ∂P.worldLaw π.seedLaw,
      ‖(w * π.realizedReward ω + c * π.realizedDuration ω) * Z ω -
        F (ω.1, (ω.2.1, ()))‖ ≤ (n : ℝ) * π.coupledOutcomeError P w c ω := by
    filter_upwards [hp.quasiMeasurePreserving.ae (P.completeScore_bound_ae h hb)] with ω hZ
    have hcoef : |w * π.coupledRewardDifference P w c ω + c * π.coupledDurationDifference P w c ω| ≤
        π.coupledOutcomeError P w c ω := by
      calc
        _ ≤ |w * π.coupledRewardDifference P w c ω| + |c * π.coupledDurationDifference P w c ω| := abs_add_le _ _
        _ = w * |π.coupledRewardDifference P w c ω| + c * |π.coupledDurationDifference P w c ω| := by
          rw [abs_mul, abs_mul, abs_of_pos hw, abs_of_nonneg hc]
        _ ≤ 1 * |π.coupledRewardDifference P w c ω| + 1 * |π.coupledDurationDifference P w c ω| :=
          add_le_add (mul_le_mul_of_nonneg_right hw1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hc1 (abs_nonneg _))
        _ = _ := by simp only [one_mul]; rfl
    have he : (w * π.realizedReward ω + c * π.realizedDuration ω) * Z ω -
        F (ω.1, (ω.2.1, ())) =
        (w * π.coupledRewardDifference P w c ω + c * π.coupledDurationDifference P w c ω) * Z ω := by
      dsimp [F, π₀, Z, coupledRewardDifference, coupledDurationDifference,
        RandomizedPolicy.realizedReward, RandomizedPolicy.realizedDuration,
        Instance.valuePolicy, Instance.canonicalRule]
      ring
    rw [he, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul hcoef hZ (abs_nonneg _) (π.coupledOutcomeError_nonnegative P w c ω)).trans_eq (mul_comm _ _)
  have hn := norm_integral_le_of_norm_le
    ((π.integrable_coupledOutcomeError P (P.integrable_maximum_of_bounded hbound) hw hc).const_mul (n : ℝ)) hnorm
  rw [integral_const_mul] at hn
  exact hn

/-- A total real parameterization of the likelihood family. Only the prescribed
interval is used in the calculus; its extension outside that interval is constant. -/
noncomputable def Instance.likelihoodPath (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) (θ : ℝ) : Instance n :=
  if hθ : |θ| ≤ 1 / 4 then P.likelihoodTilt h hh hb hm θ hθ else P

lemma Instance.likelihoodPath_of_mem (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    P.likelihoodPath h hh hb hm θ = P.likelihoodTilt h hh hb hm θ hθ := by
  simp only [likelihoodPath, dif_pos hθ]

@[simp] lemma Instance.likelihoodPath_zero (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) :
    P.likelihoodPath h hh hb hm 0 = P := by
  rw [P.likelihoodPath_of_mem h hh hb hm (by norm_num : |(0 : ℝ)| ≤ 1 / 4)]
  apply Instance.ext_law
  funext i
  simp [Instance.likelihoodTilt, ProphetSecretary.Probability.tiltLaw, ProphetSecretary.Probability.tiltFactor]

lemma optimalScalarValue_eq_sSup_range (P : Instance n) (w c : ℝ) :
    optimalScalarValue P w c = sSup (range fun π : RandomizedPolicy n => π.scalarObjective P w c) := by
  unfold optimalScalarValue
  congr 1
  ext v
  constructor
  · rintro ⟨π, hπ⟩
    exact ⟨π, hπ.symm⟩
  · rintro ⟨π, hπ⟩
    exact ⟨π, hπ.symm⟩

/-- Finite likelihood part of `lem:envelopes`, for normalized positive weights.
The derivative of the optimized value equals the complete-score expectation of
the fixed base-optimal policy. Neither an optimizer at the perturbed law nor a
differentiable choice of optimizers is assumed. -/
theorem Instance.hasDerivAt_optimalScalarValue_likelihoodPath_normalized (P : Instance n)
    {H w c : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hw : 0 < w) (hc : 0 < c) (hsum : w + c = 1)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) :
    HasDerivAt (fun θ => optimalScalarValue (P.likelihoodPath h hh hb hm θ) w c)
      ((P.valuePolicy (P.integrable_maximum_of_bounded hbound) hw.le hc.le).scalarLikelihoodDerivative
        P w c h) 0 := by
  let π₀ := P.valuePolicy (P.integrable_maximum_of_bounded hbound) hw.le hc.le
  let J : ℝ → RandomizedPolicy n → ℝ := fun θ π =>
    π.scalarObjective (P.likelihoodPath h hh hb hm θ) w c
  let D : RandomizedPolicy n → ℝ := fun π => π.scalarLikelihoodDerivative P w c h
  let A := 2 * (w * H + c) * ProphetSecretary.Probability.information P.law h
  let B := (w * H + c) * (n : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity) (ProphetSecretary.Probability.information_nonnegative P.law h)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hzero (π : RandomizedPolicy n) : J 0 π = π.scalarObjective P w c := by
    simp only [J, Instance.likelihoodPath_zero]
  have hbase : ∀ π, J 0 π ≤ J 0 π₀ := by
    intro π
    rw [hzero, hzero]
    exact (scalarObjective_le_optimal π P (P.integrable_maximum_of_bounded hbound) hw.le hc.le).trans_eq
      (P.valuePolicy_optimal (P.integrable_maximum_of_bounded hbound) hw hc.le).symm
  have hD : ∀ π, |D π| ≤ B := fun π =>
    π.scalarLikelihoodDerivative_bound P hH hbound hw.le hc.le h hb
  have hTaylor : ∀ θ, |θ| ≤ 1 / 4 → ∀ π,
      |J θ π - J 0 π - θ * D π| ≤ A * θ ^ 2 := by
    intro θ hθ π
    rw [hzero]
    dsimp only [J, D]
    rw [P.likelihoodPath_of_mem h hh hb hm hθ]
    have ht := π.scalarObjective_likelihood_taylor P hH hbound hw.le hc.le h hh hb hm hθ
    change |π.scalarObjective _ w c - π.scalarObjective P w c -
      θ * π.scalarLikelihoodDerivative P w c h| ≤ _ at ht
    convert ht using 1
    dsimp [A]
    ring
  have hStable : ∀ ε, 0 < ε → ∃ η, 0 < η ∧
      ∀ π, J 0 π₀ - J 0 π ≤ η → |D π - D π₀| ≤ ε := by
    intro ε hε
    have hδ : 0 < min w c := lt_min hw hc
    have hsmall := finite_small_outcome_errors (fun _ : Unit => n) (fun _ => P) hH hδ
      (fun _ => hbound) (fun d _ => ⟨P.tailCount d, fun _ => le_rfl⟩)
    obtain ⟨η, hη, hE⟩ := hsmall (ε / ((n : ℝ) + 1)) (by positivity)
    refine ⟨η, hη, ?_⟩
    intro π hr
    rw [hzero, hzero, P.valuePolicy_optimal (P.integrable_maximum_of_bounded hbound) hw hc.le] at hr
    have he := hE () w c (min_le_left _ _) (min_le_right _ _) hsum π hr
    have hd := π.scalarLikelihoodDerivative_difference_le P hH hbound hw hc.le
      (by linarith : w ≤ 1) (by linarith : c ≤ 1) h hh hb
    have hn := (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mp he
    exact hd.trans (by nlinarith [π.expectedOutcomeError_nonnegative P w c])
  have hderiv := ProphetSecretary.Analysis.hasDerivAt_supremum_of_stable_payoffs J D π₀ hA hB
    (by norm_num : (0 : ℝ) < 1 / 4) hbase hD hTaylor hStable
  have heq : (fun θ => optimalScalarValue (P.likelihoodPath h hh hb hm θ) w c) =
      (fun θ => sSup (range (J θ))) := by
    funext θ
    exact optimalScalarValue_eq_sSup_range _ _ _
  rw [heq]
  exact hderiv

lemma Instance.likelihoodPath_bounded (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) (θ : ℝ)
    {H : ℝ} (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    ∀ i, ∀ᵐ x ∂(P.likelihoodPath h hh hb hm θ).law i, x ≤ H := by
  unfold likelihoodPath
  split_ifs with hθ
  · exact P.likelihoodTilt_bounded h hh hb hm θ hθ hbound
  · exact hbound

/-- Finite likelihood part of `lem:envelopes` for all positive scalar weights.
The policy in the derivative is fixed at the base law and is proved optimal for
the unrestricted class of randomized history-dependent policies. -/
theorem Instance.hasDerivAt_optimalScalarValue_likelihoodPath (P : Instance n)
    {H w c : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hw : 0 < w) (hc : 0 < c)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) :
    HasDerivAt (fun θ => optimalScalarValue (P.likelihoodPath h hh hb hm θ) w c)
      ((P.valuePolicy (P.integrable_maximum_of_bounded hbound) hw.le hc.le).scalarLikelihoodDerivative
        P w c h) 0 := by
  let s := w + c
  have hs : 0 < s := add_pos hw hc
  let wn := w / s
  let cn := c / s
  have hwn : 0 < wn := div_pos hw hs
  have hcn : 0 < cn := div_pos hc hs
  have hsum : wn + cn = 1 := by dsimp [wn, cn, s]; rw [← add_div, div_self hs.ne']
  have heqw : s * wn = w := by dsimp [wn]; field_simp
  have heqc : s * cn = c := by dsimp [cn]; field_simp
  have hscaled := (P.hasDerivAt_optimalScalarValue_likelihoodPath_normalized
    hH hbound hwn hcn hsum h hh hb hm).const_mul s
  have hfunction : (fun θ => optimalScalarValue (P.likelihoodPath h hh hb hm θ) w c) =
      (fun θ => s * optimalScalarValue (P.likelihoodPath h hh hb hm θ) wn cn) := by
    funext θ
    have hp := (P.likelihoodPath h hh hb hm θ).integrable_maximum_of_bounded
      (P.likelihoodPath_bounded h hh hb hm θ hbound)
    rw [← optimalScalarValue_smul _ hp hs.le hwn.le hcn.le, heqw, heqc]
  let hP := P.integrable_maximum_of_bounded hbound
  have hratio : cn / wn = c / w := by
    dsimp [cn, wn]
    field_simp
  have hrule : P.canonicalRule wn cn = P.canonicalRule w c := by
    unfold Instance.canonicalRule
    congr 1
    funext r A t i
    rw [P.valueThreshold_rewardNormalized hP hwn hcn.le,
      P.valueThreshold_rewardNormalized hP hw hc.le, hratio]
  have hderivative : s * (P.valuePolicy hP hwn.le hcn.le).scalarLikelihoodDerivative P wn cn h =
      (P.valuePolicy hP hw.le hc.le).scalarLikelihoodDerivative P w c h := by
    change s * (∫ ω : ProphetSecretary.Model.World n Unit,
      (wn * (P.canonicalRule wn cn).reward () Finset.univ ω.1 ω.2.1 +
        cn * (P.canonicalRule wn cn).stoppingTime () Finset.univ ω.1 ω.2.1) *
          ProphetSecretary.Probability.completeScore h ω.1 ∂P.worldLaw (Measure.dirac ())) =
      ∫ ω : ProphetSecretary.Model.World n Unit,
        (w * (P.canonicalRule w c).reward () Finset.univ ω.1 ω.2.1 +
          c * (P.canonicalRule w c).stoppingTime () Finset.univ ω.1 ω.2.1) *
            ProphetSecretary.Probability.completeScore h ω.1 ∂P.worldLaw (Measure.dirac ())
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      rw [hrule]
      calc
        _ = ((s * wn) * (P.canonicalRule w c).reward () Finset.univ ω.1 ω.2.1 +
          (s * cn) * (P.canonicalRule w c).stoppingTime () Finset.univ ω.1 ω.2.1) *
            ProphetSecretary.Probability.completeScore h ω.1 := by ring
        _ = _ := by rw [heqw, heqc]
  rw [hderivative] at hscaled
  rw [hfunction]
  exact hscaled

end ProphetSecretary.Model
