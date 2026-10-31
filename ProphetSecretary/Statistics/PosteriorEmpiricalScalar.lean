import ProphetSecretary.Statistics.FinitePriorExperiment

/-!
# An observable posterior scalar for the empirical policy

The target posterior is evaluated only on the visible training array. A
supplied projection into [4/5,hi], hi<1, gives a scalar in [1−hi,1/4] on
every raw observation. Its identity with the actual conditional-expectation
posterior is an analytical almost-sure statement.
-/

open MeasureTheory Set Filter
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def posteriorEmpiricalScalar (F : FinitePrior n) (N b k : ℕ) (ρ : ℝ → ℝ)
    (d : ValueArray n N) : ℝ :=
  (1-ρ (F.boundedPosteriorFromObservation N b k d))/ρ (F.boundedPosteriorFromObservation N b k d)

lemma measurable_posteriorEmpiricalScalar (F : FinitePrior n) (N b k : ℕ)
    {ρ : ℝ → ℝ} (hρ : Measurable ρ) : Measurable (F.posteriorEmpiricalScalar N b k ρ) := by
  have h := hρ.comp (F.measurable_boundedPosteriorFromObservation N b k)
  exact (measurable_const.sub h).div h

lemma posteriorEmpiricalScalar_mem (F : FinitePrior n) (N b k : ℕ) {ρ : ℝ → ℝ} {hi : ℝ}
    (hhi : hi<1) (hρ : ∀ t∈Icc (0 : ℝ) 1, ρ t∈Icc (4/5 : ℝ) hi) (d : ValueArray n N) :
    F.posteriorEmpiricalScalar N b k ρ d∈Icc (1-hi) (1/4 : ℝ) := by
  have h := hρ _ (F.boundedPosteriorFromObservation_mem_unit N b k d)
  have hw : 0<ρ (F.boundedPosteriorFromObservation N b k d) := lt_of_lt_of_le (by norm_num) h.1
  have hOne := h.2.trans hhi.le
  have hHi0 : 0≤1-hi := sub_nonneg.mpr hhi.le
  have hMul := mul_le_mul_of_nonneg_left hOne hHi0
  constructor
  · apply (le_div_iff₀ hw).mpr
    linarith only [hMul,h.2]
  · apply (div_le_iff₀ hw).mpr
    linarith only [h.1]

lemma posteriorEmpiricalScalar_observed_eq_ae (F : FinitePrior n) (N b k : ℕ) (ρ : ℝ → ℝ) :
    (fun ω => F.posteriorEmpiricalScalar N b k ρ (F.observe N b k ω)) =ᵐ[F.law N]
      (fun ω => (1-ρ (F.posterior N b k ω))/ρ (F.posterior N b k ω)) := by
  filter_upwards [F.boundedPosterior_observed_eq_ae N b k] with ω hω
  simp only [posteriorEmpiricalScalar,hω]

lemma posteriorEmpiricalScalar_normalize (F : FinitePrior n) (N b k : ℕ) {ρ : ℝ → ℝ}
    (hρ : ∀ t∈Icc (0 : ℝ) 1, 0<ρ t) (d : ValueArray n N) :
    1/(1+F.posteriorEmpiricalScalar N b k ρ d)=ρ (F.boundedPosteriorFromObservation N b k d) ∧
      F.posteriorEmpiricalScalar N b k ρ d/(1+F.posteriorEmpiricalScalar N b k ρ d)=
        1-ρ (F.boundedPosteriorFromObservation N b k d) := by
  let w := ρ (F.boundedPosteriorFromObservation N b k d)
  have hw : 0<w := hρ _ (F.boundedPosteriorFromObservation_mem_unit N b k d)
  have hOne : 1+(1-w)/w=1/w := by
    field_simp
    ring
  change 1/(1+(1-w)/w)=w ∧ ((1-w)/w)/(1+(1-w)/w)=1-w
  rw [hOne]
  constructor
  · simp
  · field_simp

end ProphetSecretary.Statistics.FinitePrior
