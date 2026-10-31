import ProphetSecretary.Probability.CandidateValue
import ProphetSecretary.Model.ThresholdDurationMonotonicity

/-!
# Actual duration conditional on one offer value

The candidate value is replaced independently inside the full execution. The
resulting conditional-duration function is measurable and lies in [0,1]. Its
value antitonicity is proved only for Markov threshold rules, and in particular
for the actual canonical optimizer, using the derived pathwise comparison.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def Policy.durationAtValue (π : Policy Seed n) (i : Fin n)
    (z : World n Seed × ℝ) : ℝ :=
  π.stoppingTime z.1.2.2 Finset.univ (Function.update z.1.1 i z.2) z.1.2.1

lemma Policy.measurable_durationAtValue (π : Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n) :
    Measurable (π.durationAtValue i) :=
  π.measurable_stoppingTime hπ (by fun_prop) (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ

noncomputable def Policy.conditionalDurationAtValue (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) (i : Fin n) (a : ℝ) : ℝ :=
  ∫ ω, π.durationAtValue i (ω,a) ∂P.worldLaw ν

lemma Policy.measurable_conditionalDurationAtValue (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Measurable (π.conditionalDurationAtValue P ν i) :=
  (π.measurable_durationAtValue hπ i).stronglyMeasurable.integral_prod_left'.measurable

lemma Policy.integrable_durationAtValue_fixed (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) (a : ℝ) :
    Integrable (fun ω : World n Seed => π.durationAtValue i (ω,a)) (P.worldLaw ν) := by
  have hm : Measurable (fun ω : World n Seed => π.durationAtValue i (ω,a)) :=
    (π.measurable_durationAtValue hπ i).comp (measurable_id.prodMk measurable_const)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hu
  change ‖π.stoppingTime ω.2.2 Finset.univ (Function.update ω.1 i a) ω.2.1‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (π.stoppingTime_nonneg _ _ _ _ (fun j => (hu j).1))]
  exact π.stoppingTime_le_one _ _ _ _

lemma Policy.conditionalDurationAtValue_mem_unit (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) (a : ℝ) :
    π.conditionalDurationAtValue P ν i a ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hu
    exact π.stoppingTime_nonneg _ _ _ _ (fun j => (hu j).1)
  · have hi := integral_mono (π.integrable_durationAtValue_fixed hπ P ν i a) (integrable_const (1 : ℝ))
      (fun ω => π.stoppingTime_le_one ω.2.2 Finset.univ (Function.update ω.1 i a) ω.2.1)
    simpa only [Policy.conditionalDurationAtValue,integral_const,probReal_univ,one_smul] using hi

/-- No claim of this kind is made for a general history-dependent policy. -/
theorem thresholdPolicy.conditionalDurationAtValue_antitone
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ)
    (hπ : (thresholdPolicy θ).IsMeasurable) (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) :
    Antitone ((thresholdPolicy θ).conditionalDurationAtValue P ν i) := by
  intro a b hab
  apply integral_mono ((thresholdPolicy θ).integrable_durationAtValue_fixed hπ P ν i b)
    ((thresholdPolicy θ).integrable_durationAtValue_fixed hπ P ν i a)
  intro ω
  exact thresholdPolicy.stoppingTime_antitone_candidateValue θ ω.2.2 Finset.univ ω.1 ω.2.1 i hab

/-- Actual canonical conditional duration; all random inputs except the fixed
candidate value are integrated under their original independent laws. -/
theorem Instance.canonical_conditionalDurationAtValue_antitone (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (Q : Instance n) (i : Fin n) :
    Antitone ((P.valuePolicy hP hw hc).rule.conditionalDurationAtValue Q (Measure.dirac ()) i) :=
  thresholdPolicy.conditionalDurationAtValue_antitone _ (P.valueThreshold_policy_isMeasurable hP hw hc) Q (Measure.dirac ()) i

/-- Independent candidate replacement and Fubini give the actual weighted
duration identity for every measurable policy, including all past zero IDs. -/
theorem Policy.integral_duration_value_weight (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ a, |φ a| ≤ 1) :
    (∫ ω : World n Seed, φ (ω.1 i) * π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw ν) =
      ∫ a, φ a * π.conditionalDurationAtValue P ν i a ∂P.law i := by
  let F : World n Seed → ℝ := fun ω => φ (ω.1 i) * π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
  have hFm : Measurable F := (hφ.comp ((measurable_pi_apply i).comp measurable_fst)).mul
    (π.measurable_stoppingTime hπ (by fun_prop) (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ)
  have hFI : Integrable F (P.worldLaw ν) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable 1
    filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hu
    change ‖φ (ω.1 i) * π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1‖ ≤ 1
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (π.stoppingTime_nonneg _ _ _ _ (fun j => (hu j).1))]
    exact mul_le_one₀ (hb _) (π.stoppingTime_nonneg _ _ _ _ (fun j => (hu j).1)) (π.stoppingTime_le_one _ _ _ _)
  have hp := P.replaceValue_measurePreserving ν i
  have he := integral_map (μ := (P.worldLaw ν).prod (P.law i)) hp.measurable.aemeasurable hFm.aestronglyMeasurable
  rw [hp.map_eq] at he
  calc
    _ = ∫ z, F (Instance.replaceValue i z) ∂(P.worldLaw ν).prod (P.law i) := he
    _ = ∫ a, (∫ ω, F (Instance.replaceValue i (ω,a)) ∂P.worldLaw ν) ∂P.law i :=
      integral_prod_symm _ (hp.integrable_comp_of_integrable hFI)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun a => by
        change (∫ ω : World n Seed, φ ((Function.update ω.1 i a) i) *
          π.stoppingTime ω.2.2 Finset.univ (Function.update ω.1 i a) ω.2.1 ∂P.worldLaw ν) = _
        simp only [Function.update_self]
        rw [integral_const_mul]
        rfl

end ProphetSecretary.Model
