import ProphetSecretary.Limiting.PoissonObservableWeak
import ProphetSecretary.Limiting.ZeroIntensity

/-!
# Vanishing-intensity convergence without normalized-mark convergence

The error from replacing a configuration by the empty one is at most three
times the linear-growth constant times the total intensity. This includes
count-weighted observables and is uniform in the independent auxiliary law.
-/
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology Classical NNReal ENNReal
namespace ProphetSecretary.Limiting
variable {Aux : Type*} [MeasurableSpace Aux]

lemma configuration_eq_empty_of_count_zero (ω : Configuration) (h : ω.1=0) : ω=emptyConfiguration := by
  rcases ω with ⟨N,pts⟩
  change N=0 at h
  subst N
  change configurationMk 0 pts=configurationMk 0 (fun j => Fin.elim0 j)
  congr 1
  funext j
  exact Fin.elim0 j

lemma poissonObservable_empty_error (μ : FiniteMeasure ℝ) (ν : Measure Aux)
    [IsProbabilityMeasure ν] (f : Configuration × Aux → ℝ) (hf : Measurable f)
    {D : ℝ} (hD : 0≤D) (hb : ∀ q, |f q|≤D*((q.1.1:ℝ)+1)) :
    |(∫ q, f q ∂worldLaw μ ν)-(∫ r, f (emptyConfiguration,r) ∂ν)| ≤ 3*D*(μ.mass:ℝ) := by
  have hEmptyMeas : Measurable (fun r : Aux => f (emptyConfiguration,r)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hEmptyBound (r : Aux) : |f (emptyConfiguration,r)|≤D := by
    simpa only [emptyConfiguration,configurationMk,Nat.cast_zero,zero_add,mul_one] using hb (emptyConfiguration,r)
  have hEmptyI : Integrable (fun r : Aux => f (emptyConfiguration,r)) ν :=
    Integrable.of_bound hEmptyMeas.aestronglyMeasurable D
      (Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using hEmptyBound r))
  have hs : MeasurePreserving (Prod.snd : Configuration × Aux → Aux) (worldLaw μ ν) ν := measurePreserving_snd
  have hEmptyWorldI := hs.integrable_comp_of_integrable hEmptyI
  have hCount : Integrable (fun q : Configuration × Aux => (q.1.1:ℝ)) (worldLaw μ ν) :=
    (measurePreserving_fst (μ := configurationLaw μ) (ν := ν)).integrable_comp_of_integrable
      (configuration_count_integrable μ)
  have hPoint (q : Configuration × Aux) :
      |f q-f (emptyConfiguration,q.2)| ≤ 3*D*(q.1.1:ℝ) := by
    by_cases hN : q.1.1=0
    · have hq : q.1=emptyConfiguration := configuration_eq_empty_of_count_zero q.1 hN
      have hfEq : f q=f (emptyConfiguration,q.2) := congrArg f (Prod.ext hq rfl)
      rw [hfEq,sub_self,abs_zero]
      positivity
    · have hN1 : (1:ℝ)≤(q.1.1:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
      have hTriangle := abs_sub (f q) (f (emptyConfiguration,q.2))
      have hbound := hb q
      have he := hEmptyBound q.2
      nlinarith
  rw [← hs.hasLaw.integral_comp hEmptyMeas.aestronglyMeasurable,
    ← integral_sub (poissonObservable_integrable_of_linear_count μ ν f hf hb) hEmptyWorldI]
  have hNorm := norm_integral_le_of_norm_le (f := fun q => f q-f (emptyConfiguration,q.2)) (hCount.const_mul (3*D))
    (Eventually.of_forall (fun q => by
      change |f q-f (emptyConfiguration,q.2)|≤3*D*(q.1.1:ℝ)
      exact hPoint q))
  have hFirst : (∫ q : Configuration × Aux, (q.1.1:ℝ) ∂worldLaw μ ν)=(μ.mass:ℝ) := by
    have he := (measurePreserving_fst (μ := configurationLaw μ) (ν := ν)).hasLaw.integral_comp
      ((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp measurable_configuration_count).aestronglyMeasurable
    exact he.trans (configuration_count_expectation μ)
  change |∫ q, f q-f (emptyConfiguration,q.2) ∂worldLaw μ ν|≤3*D*(μ.mass:ℝ)
  simpa only [Real.norm_eq_abs,integral_const_mul,hFirst] using hNorm
end ProphetSecretary.Limiting
