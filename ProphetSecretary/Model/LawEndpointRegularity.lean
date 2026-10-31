import ProphetSecretary.Model.LawHorizonContinuity
import ProphetSecretary.Model.LawStateBranches
import ProphetSecretary.Probability.WideLikelihoodAbsoluteContinuity
import ProphetSecretary.Analysis.LevelSetDerivative

/-!
# Initial-root equalities under arbitrary offer laws

A deterministic continuation curve is compared with the random candidate
level. Fubini removes only the nonzero derivative on that level set, so atoms
need not be enumerated and the level event itself may have positive mass.
Absolute continuity transfers the statement to each actual perturbed law.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Instance.world_clocks_lt_one_ae (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ i, ω.2.1 i < 1 := by
  have hne : ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ i, ω.2.1 i ≠ 1 :=
    ae_all_iff.mpr (fun i ↦ (P.world_clock_measurePreserving ν i).quasiMeasurePreserving.ae (Instance.uniformClock.ae_ne 1))
  filter_upwards [P.world_clocks_mem_unitInterval ν, hne] with ω hω hn
  exact fun i ↦ lt_of_le_of_ne (hω i).2 (hn i)

lemma Instance.world_values_mem_Icc_ae (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {H : ℝ} (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ i, ω.1 i ∈ Icc (0 : ℝ) H := by
  have hp : MeasurePreserving (fun ω : World n Seed ↦ ω.1) (P.worldLaw ν) P.valuesLaw := measurePreserving_fst
  have hb : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ H :=
    ae_all_iff.mpr (fun i ↦ (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hbound i))
  filter_upwards [hp.quasiMeasurePreserving.ae P.ae_nonnegative, hp.quasiMeasurePreserving.ae hb] with ω h0 hH
  exact fun i ↦ ⟨h0 i, hH i⟩

lemma Instance.initial_level_derivative_zero_ae (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c H : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (i : Fin n) (A : Finset (Fin n)) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-(1 / 4) : ℝ) (1 / 4)),
      ∀ᵐ ω : World n Seed ∂(P.likelihoodWidePath h hh hb hm θ).worldLaw ν,
        optimalScalarValue (((P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
          (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j))
          (fun j ↦ hm (stateEmbedding A j)) θ)) w c = w * ω.1 i →
        deriv (fun q ↦ optimalScalarValue (((P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
          (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j))
          (fun j ↦ hm (stateEmbedding A j)) q)) w c) θ = 0 := by
  let f := fun q ↦ optimalScalarValue ((P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) q) w c
  have hJoint := (P.restrictTo A).likelihoodValue_joint_continuousOn hw hH (fun j ↦ hbound (stateEmbedding A j))
    (fun j ↦ h (stateEmbedding A j)) (fun j ↦ hh (stateEmbedding A j))
    (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j))
  have hMap : ContinuousOn (fun q : ℝ ↦ (q, c)) (Ioo (-(1 / 2) : ℝ) (1 / 2)) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hComp := hJoint.comp hMap (fun q hq ↦ ⟨hq, hc⟩)
  have hCont : ContinuousOn f (Ioo (-(1 / 2) : ℝ) (1 / 2)) := by
    convert hComp using 1
    funext q
    rfl
  have hBase := ProphetSecretary.Analysis.ae_derivative_zero_on_random_level_interval (P.worldLaw ν) f hCont
    (fun ω : World n Seed ↦ w * ω.1 i) (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))
  have hSub : Ioo (-(1 / 4) : ℝ) (1 / 4) ⊆ Ioo (-(1 / 2) : ℝ) (1 / 2) := by
    intro θ hθ
    constructor <;> linarith [hθ.1, hθ.2]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hSub hBase,
    ae_restrict_mem measurableSet_Ioo] with θ hθ hmem
  have hAbs : |θ| ≤ 1 / 4 := abs_le.mpr ⟨hmem.1.le, hmem.2.le⟩
  exact (P.likelihoodWidePath_worldLaw_absolutelyContinuous_quarter ν h hh hb hm hAbs).ae_le hθ

lemma Instance.all_initial_levels_derivative_zero_ae (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c H : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-(1 / 4) : ℝ) (1 / 4)),
      ∀ᵐ ω : World n Seed ∂(P.likelihoodWidePath h hh hb hm θ).worldLaw ν,
        ∀ (i : Fin n) (A : Finset (Fin n)),
          optimalScalarValue (((P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
            (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j))
            (fun j ↦ hm (stateEmbedding A j)) θ)) w c = w * ω.1 i →
          deriv (fun q ↦ optimalScalarValue (((P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
            (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j))
            (fun j ↦ hm (stateEmbedding A j)) q)) w c) θ = 0 := by
  have hAll := ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (fun A ↦ P.initial_level_derivative_zero_ae ν hw hc hH hbound h hh hb hm i A))
  filter_upwards [hAll] with θ hθ
  exact ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (fun A ↦ hθ i A))

end ProphetSecretary.Model
