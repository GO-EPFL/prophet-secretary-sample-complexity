import ProphetSecretary.Limiting.CountablePoissonCounts
import ProphetSecretary.Limiting.GeneratingFunctionalIntensity
import Mathlib.Probability.Independence.Integration

/-!
# Generating functionals and restricted intensities of actual bands

Finite superposition is proved on the actual independent band product law.
Restriction above the reserve involves only finitely many band intensities.
-/

open MeasureTheory ProbabilityTheory Set Filter Complex
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance)

instance intensity_sfinite : SFinite B.intensity := by
  rw [← B.sum_bandIntensity]
  infer_instance

theorem finiteBands_generating_functional (N : ℕ) (g : Point → ℂ)
    (hg : Measurable g) (hb : ∀ p, ‖g p‖ ≤ 1) :
    (∫ ω, ∏ k : Fin N, pointProd g (ω k) ∂B.bandConfigurationsLaw) =
      Complex.exp (∑ k : Fin N, ∫ p, (g p-1) ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k)) := by
  have hG := measurable_pointProd hg
  have hI := (iIndepFun.precomp (g := fun k : Fin N => (k : ℕ)) Fin.val_injective
    B.bandConfigurations_independent).comp (fun _ => pointProd g) (fun _ => hG)
  have hprod : (∫ ω, ∏ k : Fin N, pointProd g (ω k) ∂B.bandConfigurationsLaw) =
      ∏ k : Fin N, ∫ ω, pointProd g (ω k) ∂B.bandConfigurationsLaw := by
    simpa only [Function.comp_def] using hI.integral_fun_prod_eq_prod_integral
      (fun k => (hG.comp (measurable_pi_apply (k : ℕ))).aestronglyMeasurable)
  rw [hprod,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro k _
  have he := (B.bandConfiguration_measurePreserving k).hasLaw.integral_comp hG.aestronglyMeasurable
  change (∫ ω, pointProd g (ω k) ∂B.bandConfigurationsLaw) = _ at he
  rw [he]
  exact generating_functional_intensity (B.bandIntensity k) g hg hb

lemma intensityAbove_eq_finsetSum {b : ℝ} (hb : (B.terminal : ℝ) < b) {K : ℕ}
    (hK : ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b) :
    (B.intensityAbove b hb : Measure ℝ) =
      ∑ k ∈ Finset.range (K+1), (B.bandIntensity k : Measure ℝ).restrict (Ioi b) := by
  ext S hS
  change (B.intensity.restrict (Ioi b)) S = _
  rw [← B.sum_bandIntensity,Measure.restrict_sum_of_countable,Measure.sum_apply _ hS]
  simp only [Measure.coe_finsetSum,Finset.sum_apply]
  apply tsum_eq_sum
  intro k hk
  have hkg : K < k := by simp only [Finset.mem_range,not_lt] at hk; omega
  rw [Measure.restrict_zero_set (B.bandIntensity_tail_zero hK k hkg)]
  simp

lemma intensityAbove_pointIntensity_eq_finsetSum {b : ℝ} (hb : (B.terminal : ℝ) < b) {K : ℕ}
    (hK : ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b) :
    ProphetSecretary.Limiting.intensity (B.intensityAbove b hb) =
      ∑ k ∈ Finset.range (K+1),
        (ProphetSecretary.Limiting.intensity (B.bandIntensity k)).restrict (univ ×ˢ Ioi b) := by
  unfold ProphetSecretary.Limiting.intensity
  have hprod (s : Finset ℕ) :
      Model.Instance.uniformClock.prod (∑ k ∈ s, (B.bandIntensity k : Measure ℝ).restrict (Ioi b)) =
        ∑ k ∈ s, Model.Instance.uniformClock.prod ((B.bandIntensity k : Measure ℝ).restrict (Ioi b)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih => rw [Finset.sum_insert hk,Measure.prod_add,ih,Finset.sum_insert hk]
  rw [B.intensityAbove_eq_finsetSum hb hK,hprod]
  apply Finset.sum_congr rfl
  intro k _
  have he := Measure.prod_restrict (μ := Model.Instance.uniformClock)
    (ν := (B.bandIntensity k : Measure ℝ)) univ (Ioi b)
  simpa only [Measure.restrict_univ] using he

/-- Every generating-functional test equal to one below b has the same law
on the actual finitely active bands and the single truncated configuration. -/
theorem finiteBands_generating_above {b : ℝ} (hb : (B.terminal : ℝ) < b) {K : ℕ}
    (hK : ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b) (g : Point → ℂ)
    (hg : Measurable g) (hn : ∀ p, ‖g p‖ ≤ 1) (hbelow : ∀ p, p.2 ≤ b → g p = 1) :
    (∫ ω, ∏ k : Fin (K+1), pointProd g (ω k) ∂B.bandConfigurationsLaw) =
      (∫ ω, pointProd g ω ∂configurationLaw (B.intensityAbove b hb)) := by
  have hInt (k : ℕ) : Integrable (fun p => g p-1) (ProphetSecretary.Limiting.intensity (B.bandIntensity k)) :=
    (Integrable.of_bound hg.aestronglyMeasurable 1 (Filter.Eventually.of_forall hn)).sub (integrable_const 1)
  have hRestr (k : ℕ) :
      (∫ p in univ ×ˢ Ioi b, (g p-1) ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k)) =
        ∫ p, (g p-1) ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    have hp' : p.2 ≤ b := by simpa only [mem_compl_iff,mem_prod,mem_univ,true_and,mem_Ioi,not_lt] using hp
    rw [hbelow p hp',sub_self]
  have hsum : (∑ k : Fin (K+1), ∫ p, (g p-1) ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k)) =
      ∫ p, (g p-1) ∂ProphetSecretary.Limiting.intensity (B.intensityAbove b hb) := by
    calc
      _ = ∑ k ∈ Finset.range (K+1), ∫ p, (g p-1) ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k) :=
        (Finset.sum_range (n := K+1) (fun k : ℕ => ∫ p, (g p-1) ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k))).symm
      _ = ∑ k ∈ Finset.range (K+1), ∫ p in univ ×ˢ Ioi b, (g p-1) ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k) :=
        Finset.sum_congr rfl (fun k _ => (hRestr k).symm)
      _ = _ := by
        rw [B.intensityAbove_pointIntensity_eq_finsetSum hb hK,integral_finsetSum_measure (fun k _ => (hInt k).restrict)]
  rw [B.finiteBands_generating_functional (K+1) g hg hn,
    generating_functional_intensity (B.intensityAbove b hb) g hg hn,hsum]

end ProphetSecretary.Limiting.CountableInstance
