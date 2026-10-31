import ProphetSecretary.Statistics.FinitePriorConditionalSampling
import ProphetSecretary.Statistics.FirstMomentClassifierError

/-!
# The finite-prior classifier and posterior excluded mass

The actual classifier sees only its preliminary h-round training prefix. The
hidden atom is used solely to analyze invalid choices. Conditional expectation
of the invalid-choice indicator is the posterior mass excluded by restricting
to the selected valid class; its expectation is the true error probability.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model ProphetSecretary.Analysis
variable {n : ℕ}

def classifierPrefixRead (n N h : ℕ) (hh : h≤N) (d : ValueArray n N) : (Fin n × Fin h) → ℝ :=
  fun q => d (q.1,prefixColumn N h hh q.2)

lemma measurable_classifierPrefixRead (n N h : ℕ) (hh : h≤N) : Measurable (classifierPrefixRead n N h hh) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

def classifierPrefix (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (ω : BaseWorld F N) : (Fin n × Fin h) → ℝ :=
  classifierPrefixRead n N h hh ω.2

lemma classifierPrefix_eq_observed (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (ω : BaseWorld F N) :
    F.classifierPrefix N h hh ω=classifierPrefixRead n N h hh (F.observe N 0 h ω) := by
  funext q
  have hmem : (q.1,prefixColumn N h hh q.2)∈trainingCoordinates n N 0 h := by
    simp only [trainingCoordinates,Finset.mem_filter,Finset.mem_univ,true_and,zero_add,Nat.min_eq_left hh,prefixColumn]
    exact q.2.is_lt
  change ω.2 _=if _ then ω.2 _ else 0
  rw [if_pos hmem]

lemma classifierPrefix_stronglyMeasurable (F : FinitePrior n) (N h : ℕ) (hh : h≤N) :
    StronglyMeasurable[F.dataSigma N 0 h] (F.classifierPrefix N h hh) := by
  have hm : @Measurable (BaseWorld F N) (ValueArray n N) (F.dataSigma N 0 h) _ (F.observe N 0 h) :=
    Measurable.of_comap_le le_rfl
  convert (measurable_classifierPrefixRead n N h hh).stronglyMeasurable.comp_measurable hm using 1
  funext ω
  exact F.classifierPrefix_eq_observed N h hh ω

lemma classifierPrefix_atom_measurePreserving (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (θ : Fin F.size) :
    MeasurePreserving (F.classifierPrefix N h hh) (F.atomLaw N θ) ((F.offerInstance θ).trainingCoordinateLaw h) :=
  ((measurePreserving_fst (μ:=(F.offerInstance θ).trainingCoordinateLaw h) (ν:=(F.offerInstance θ).valuesLaw)).comp
    (prefixOnlineValues_measurePreserving (F.offerInstance θ) N h hh)).comp
      (measurePreserving_snd (μ:=Measure.dirac θ))

def invalidClassifierSet (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) : Set (BaseWorld F N) :=
  {ω | F.classifierPrefix N h hh ω∈invalidFirstMomentClass Sstar (F.offerInstance ω.1).totalFirstMoment}

lemma measurableSet_invalidClassifierSet (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) :
    MeasurableSet (F.invalidClassifierSet N h hh Sstar) := by
  have hPrefix := (F.classifierPrefix_stronglyMeasurable N h hh).mono (F.dataSigma_le N 0 h)
  have hEq : F.invalidClassifierSet N h hh Sstar=
      ⋃ θ : Fin F.size, {ω : BaseWorld F N | ω.1=θ}∩
        (F.classifierPrefix N h hh) ⁻¹' invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment := by
    ext ω
    simp only [invalidClassifierSet,Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_preimage]
    constructor
    · exact fun h => ⟨ω.1,rfl,h⟩
    · rintro ⟨θ,hθ,h⟩
      simpa only [hθ] using h
  rw [hEq]
  exact MeasurableSet.iUnion fun θ =>
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((measurableSet_invalidFirstMomentClass Sstar _).preimage hPrefix.measurable)

noncomputable def invalidClassifierIndicator (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) : BaseWorld F N → ℝ :=
  (F.invalidClassifierSet N h hh Sstar).indicator 1

lemma invalidClassifierIndicator_mem_unit (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) (ω : BaseWorld F N) :
    F.invalidClassifierIndicator N h hh Sstar ω∈Icc (0:ℝ) 1 := by
  simp only [invalidClassifierIndicator,Set.indicator_apply,Pi.one_apply]
  split_ifs <;> norm_num

lemma measurable_invalidClassifierIndicator (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) :
    Measurable (F.invalidClassifierIndicator N h hh Sstar) :=
  measurable_const.indicator (F.measurableSet_invalidClassifierSet N h hh Sstar)

lemma invalidClassifierIndicator_integrable (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (μ : Measure (BaseWorld F N)) [IsFiniteMeasure μ] : Integrable (F.invalidClassifierIndicator N h hh Sstar) μ :=
  Integrable.of_bound (F.measurable_invalidClassifierIndicator N h hh Sstar).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (F.invalidClassifierIndicator_mem_unit N h hh Sstar ω).1]
      exact (F.invalidClassifierIndicator_mem_unit N h hh Sstar ω).2)

/-- The atomwise error uses actual independent training columns. -/
lemma integral_invalidClassifierIndicator_atom (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ)
    (θ : Fin F.size) :
    (∫ ω, F.invalidClassifierIndicator N h hh Sstar ω ∂F.atomLaw N θ)=
      ((F.offerInstance θ).trainingCoordinateLaw h).real
        (invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment) := by
  let g : ((Fin n × Fin h) → ℝ) → ℝ :=
    (invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment).indicator 1
  have hDirac : ∀ᵐ t ∂Measure.dirac θ, t=θ := by simp
  have hHidden : ∀ᵐ ω ∂F.atomLaw N θ, ω.1=θ :=
    (measurePreserving_fst (μ:=Measure.dirac θ)).quasiMeasurePreserving.ae hDirac
  have hEq : F.invalidClassifierIndicator N h hh Sstar =ᵐ[F.atomLaw N θ]
      (fun ω => g (F.classifierPrefix N h hh ω)) := by
    filter_upwards [hHidden] with ω hω
    simp only [invalidClassifierIndicator,Set.indicator_apply,Pi.one_apply,invalidClassifierSet,Set.mem_setOf_eq,hω,g]
  rw [integral_congr_ae hEq]
  have hMP := F.classifierPrefix_atom_measurePreserving N h hh θ
  have hg : Measurable g := measurable_const.indicator (measurableSet_invalidFirstMomentClass Sstar _)
  have hMap := integral_map (μ:=F.atomLaw N θ) hMP.measurable.aemeasurable hg.aestronglyMeasurable
  rw [hMP.map_eq] at hMap
  exact hMap.symm.trans (integral_indicator_one (measurableSet_invalidFirstMomentClass Sstar _))

/-- The finite prior has the same error bound, without independence between the
hidden target and the ONLINE vector after averaging over the prior. -/
theorem integral_invalidClassifierIndicator_le (F : FinitePrior n) (N m : ℕ)
    (hN : classifierRounds m≤N) (hm : 2≤m)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) {Sstar : ℝ} (hS : 1≤Sstar) :
    (∫ ω, F.invalidClassifierIndicator N (classifierRounds m) hN Sstar ω ∂F.law N)≤1/(m:ℝ)^4 := by
  unfold law
  rw [integral_finsetSum_measure (fun θ _ =>
    (F.invalidClassifierIndicator_integrable N _ hN Sstar (F.atomLaw N θ)).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul,F.integral_invalidClassifierIndicator_atom]
  calc
    (∑ θ : Fin F.size, (F.weight θ:ℝ)*((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
        (invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment))≤
      ∑ θ : Fin F.size, (F.weight θ:ℝ)*(1/(m:ℝ)^4) :=
      Finset.sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left
        (firstMomentClassifier_invalid_probability (F.offerInstance θ) (hcap θ) hm hS) (F.weight θ).coe_nonneg
    _=1/(m:ℝ)^4 := by
      rw [←Finset.sum_mul]
      have hW : (∑ θ : Fin F.size, (F.weight θ:ℝ))=1 := by exact_mod_cast F.weight_sum
      rw [hW,one_mul]

/-- The posterior mass discarded by restricting to the selected valid class. -/
noncomputable def posteriorExcludedMass (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) : BaseWorld F N → ℝ :=
  (F.law N)[F.invalidClassifierIndicator N h hh Sstar|F.dataSigma N 0 h]

lemma posteriorExcludedMass_mem_unit (F : FinitePrior n) (N h : ℕ) (hh : h≤N) (Sstar : ℝ) :
    ∀ᵐ ω ∂F.law N, F.posteriorExcludedMass N h hh Sstar ω∈Icc (0:ℝ) 1 := by
  exact ProphetSecretary.Probability.conditionalPosterior_mem_unit
    (ℱ:=F.dataFiltration N 0) (F.measurable_invalidClassifierIndicator N h hh Sstar)
    (Eventually.of_forall (F.invalidClassifierIndicator_mem_unit N h hh Sstar)) h

/-- Source E[xi]≤m^(-4), with xi an actual conditional expectation given the
classifier's observed prefix. No posterior-normalization claim is assumed. -/
theorem integral_posteriorExcludedMass_le (F : FinitePrior n) (N m : ℕ)
    (hN : classifierRounds m≤N) (hm : 2≤m)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) {Sstar : ℝ} (hS : 1≤Sstar) :
    (∫ ω, F.posteriorExcludedMass N (classifierRounds m) hN Sstar ω ∂F.law N)≤1/(m:ℝ)^4 := by
  change (∫ ω, (F.law N)[F.invalidClassifierIndicator N (classifierRounds m) hN Sstar|
    F.dataSigma N 0 (classifierRounds m)] ω ∂F.law N)≤_
  rw [integral_condExp (F.dataSigma_le N 0 (classifierRounds m))]
  exact F.integral_invalidClassifierIndicator_le N m hN hm hcap hS

end ProphetSecretary.Statistics.FinitePrior
