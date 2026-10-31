import ProphetSecretary.Model.TrainingCoordinates
import ProphetSecretary.Probability.RevealedCoordinates
import ProphetSecretary.Probability.PosteriorMartingale
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# A finite prior on product instances and hidden payoff targets

Prior atoms enumerate pairs (P,J); repeated instances with different targets are
allowed. Conditional on an atom, every stored value coordinate is an independent
draw from its stated marginal. The last column is the ONLINE offer vector; only
preceding columns are training. Observation at stage k reveals the first b+k
training rounds, where b permits preliminary class-selection data. The last
column is excluded from every training observation, including after saturation.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

structure FinitePrior (n : ℕ) where
  size : ℕ
  weight : Fin size → ℝ≥0
  weight_sum : ∑ θ, weight θ=1
  offerInstance : Fin size → Instance n
  target : Fin size → Option (Fin n)

namespace FinitePrior
variable {n : ℕ}

abbrev ValueArray (n N : ℕ) := (Fin n × Fin (N+1)) → ℝ
abbrev BaseWorld (F : FinitePrior n) (N : ℕ) := Fin F.size × ValueArray n N

noncomputable def atomLaw (F : FinitePrior n) (N : ℕ) (θ : Fin F.size) : Measure (BaseWorld F N) :=
  (Measure.dirac θ).prod ((F.offerInstance θ).trainingCoordinateLaw (N+1))

instance atomLaw_probability (F : FinitePrior n) (N : ℕ) (θ : Fin F.size) :
    IsProbabilityMeasure (F.atomLaw N θ) := by unfold atomLaw; infer_instance

noncomputable def law (F : FinitePrior n) (N : ℕ) : Measure (BaseWorld F N) :=
  ∑ θ : Fin F.size, F.weight θ • F.atomLaw N θ

instance law_probability (F : FinitePrior n) (N : ℕ) : IsProbabilityMeasure (F.law N) := by
  constructor
  simp only [law,Measure.finsetSum_apply,Measure.smul_apply,measure_univ]
  simp only [ENNReal.smul_one]
  exact_mod_cast F.weight_sum

/-- The hidden target is not part of any training observation. -/
def rewardIndicator (F : FinitePrior n) {N : ℕ} (ω : BaseWorld F N) : ℝ :=
  if F.target ω.1=none then 1 else 0

lemma measurable_rewardIndicator (F : FinitePrior n) (N : ℕ) :
    Measurable (F.rewardIndicator (N:=N)) :=
  (measurable_of_finite (fun θ : Fin F.size => if F.target θ=none then (1:ℝ) else 0)).comp measurable_fst

lemma rewardIndicator_mem_unit (F : FinitePrior n) {N : ℕ} (ω : BaseWorld F N) :
    F.rewardIndicator ω∈Icc (0:ℝ) 1 := by
  unfold rewardIndicator
  split_ifs <;> norm_num

/-- A known observation count distinguishes observed zero from an unrevealed
coordinate masked by zero. The ONLINE column N is always masked. -/
def trainingCoordinates (n N b k : ℕ) : Finset (Fin n × Fin (N+1)) :=
  Finset.univ.filter fun q => q.2.val<min (b+k) N

lemma trainingCoordinates_mono (n N b : ℕ) {k l : ℕ} (hkl : k≤l) :
    trainingCoordinates n N b k ⊆ trainingCoordinates n N b l := by
  intro q hq
  simp only [trainingCoordinates,Finset.mem_filter,Finset.mem_univ,true_and] at hq ⊢
  omega

def observe (F : FinitePrior n) (N b k : ℕ) (ω : BaseWorld F N) : ValueArray n N :=
  ProphetSecretary.Probability.maskCoordinates (trainingCoordinates n N b k) ω.2

lemma measurable_observe (F : FinitePrior n) (N b k : ℕ) : Measurable (F.observe N b k) :=
  (ProphetSecretary.Probability.measurable_maskCoordinates _).comp measurable_snd

abbrev dataSigma (F : FinitePrior n) (N b k : ℕ) : MeasurableSpace (BaseWorld F N) :=
  (inferInstance : MeasurableSpace (ValueArray n N)).comap (F.observe N b k)

lemma dataSigma_le (F : FinitePrior n) (N b k : ℕ) : F.dataSigma N b k≤
    (inferInstance : MeasurableSpace (BaseWorld F N)) := (F.measurable_observe N b k).comap_le

lemma dataSigma_mono (F : FinitePrior n) (N b : ℕ) {k l : ℕ} (hkl : k≤l) :
    F.dataSigma N b k≤F.dataSigma N b l := by
  have hm : @Measurable (BaseWorld F N) (ValueArray n N) (F.dataSigma N b l) _ (F.observe N b l) :=
    Measurable.of_comap_le le_rfl
  have hcomp := (ProphetSecretary.Probability.measurable_maskCoordinates (trainingCoordinates n N b k)).comp hm
  have hk : @Measurable (BaseWorld F N) (ValueArray n N) (F.dataSigma N b l) _ (F.observe N b k) := by
    convert hcomp using 1
    funext ω
    exact (ProphetSecretary.Probability.maskCoordinates_subset (trainingCoordinates_mono n N b hkl) ω.2).symm
  exact hk.comap_le

def dataFiltration (F : FinitePrior n) (N b : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (BaseWorld F N)) where
  seq k := F.dataSigma N b k
  mono' _ _ h := F.dataSigma_mono N b h
  le' k := F.dataSigma_le N b k

noncomputable def posterior (F : FinitePrior n) (N b k : ℕ) : BaseWorld F N → ℝ :=
  ProphetSecretary.Probability.conditionalPosterior F.rewardIndicator (F.dataFiltration N b) (F.law N) k

lemma posterior_martingale (F : FinitePrior n) (N b : ℕ) :
    Martingale (F.posterior N b) (F.dataFiltration N b) (F.law N) :=
  ProphetSecretary.Probability.conditionalPosterior_martingale F.rewardIndicator

lemma posterior_mem_unit (F : FinitePrior n) (N b k : ℕ) :
    ∀ᵐ ω ∂F.law N, F.posterior N b k ω∈Icc (0:ℝ) 1 :=
  ProphetSecretary.Probability.conditionalPosterior_mem_unit (F.measurable_rewardIndicator N)
    (Eventually.of_forall F.rewardIndicator_mem_unit) k

/-- Canonical CE versions are genuinely functions of observed training data. -/
lemma posterior_stronglyMeasurable (F : FinitePrior n) (N b k : ℕ) :
    StronglyMeasurable[F.dataSigma N b k] (F.posterior N b k) := stronglyMeasurable_condExp

lemma posterior_eq_of_observe_eq (F : FinitePrior n) (N b k : ℕ)
    (ω ω' : BaseWorld F N) (h : F.observe N b k ω=F.observe N b k ω') :
    F.posterior N b k ω=F.posterior N b k ω' :=
  (F.posterior_stronglyMeasurable N b k).factorsThrough h

noncomputable def posteriorFromObservation (F : FinitePrior n) (N b k : ℕ) : ValueArray n N → ℝ :=
  Classical.choose ((F.posterior_stronglyMeasurable N b k).exists_eq_measurable_comp)

lemma stronglyMeasurable_posteriorFromObservation (F : FinitePrior n) (N b k : ℕ) :
    StronglyMeasurable (F.posteriorFromObservation N b k) :=
  (Classical.choose_spec ((F.posterior_stronglyMeasurable N b k).exists_eq_measurable_comp)).1

lemma posterior_eq_observed (F : FinitePrior n) (N b k : ℕ) (ω : BaseWorld F N) :
    F.posterior N b k ω=F.posteriorFromObservation N b k (F.observe N b k ω) :=
  congrFun (Classical.choose_spec ((F.posterior_stronglyMeasurable N b k).exists_eq_measurable_comp)).2 ω

/-- A pointwise unit-range version is available to the actual online policy. -/
noncomputable def boundedPosteriorFromObservation (F : FinitePrior n) (N b k : ℕ) (d : ValueArray n N) : ℝ :=
  max 0 (min 1 (F.posteriorFromObservation N b k d))

lemma measurable_boundedPosteriorFromObservation (F : FinitePrior n) (N b k : ℕ) :
    Measurable (F.boundedPosteriorFromObservation N b k) :=
  measurable_const.max (measurable_const.min (F.stronglyMeasurable_posteriorFromObservation N b k).measurable)

lemma boundedPosteriorFromObservation_mem_unit (F : FinitePrior n) (N b k : ℕ) (d : ValueArray n N) :
    F.boundedPosteriorFromObservation N b k d∈Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩

lemma boundedPosterior_observed_eq_ae (F : FinitePrior n) (N b k : ℕ) :
    (fun ω => F.boundedPosteriorFromObservation N b k (F.observe N b k ω)) =ᵐ[F.law N] F.posterior N b k := by
  filter_upwards [F.posterior_mem_unit N b k] with ω hω
  unfold boundedPosteriorFromObservation
  rw [←F.posterior_eq_observed N b k ω,min_eq_right hω.2,max_eq_right hω.1]

def onlineValues (F : FinitePrior n) {N : ℕ} (ω : BaseWorld F N) : Fin n → ℝ :=
  fun i => ω.2 (i,Fin.last N)

lemma measurable_onlineValues (F : FinitePrior n) (N : ℕ) : Measurable (F.onlineValues (N:=N)) :=
  measurable_pi_lambda _ (fun i => (measurable_pi_apply (i,Fin.last N)).comp measurable_snd)

lemma observe_online_column_zero (F : FinitePrior n) (N b k : ℕ) (ω : BaseWorld F N) (i : Fin n) :
    F.observe N b k ω (i,Fin.last N)=0 := by
  have h : (i,Fin.last N)∉trainingCoordinates n N b k := by
    simp only [trainingCoordinates,Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_last]
    omega
  exact if_neg h

end FinitePrior
end ProphetSecretary.Statistics
