import ProphetSecretary.Limiting.CountableBandReplacement
import ProphetSecretary.Limiting.CountableMarkovPointSets

/-!
# Mecke's identity inside the actual full countable world

An independent fresh band configuration replaces the original band. This
proved pushforward retains all other offers, clocks and independent seed.
Applying finite marked Mecke with the entire old world as independent
auxiliary randomness yields the full-world identity. This analytical
randomness and the construction counts are not policy observations.
-/
open MeasureTheory Set Filter
open scoped Classical ENNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def bandMeckeKernel (k : ℕ) (F : Point × CompleteWorld Seed → ℝ≥0∞)
    (z : Point × World (CompleteWorld Seed)) : ℝ≥0∞ :=
  F (z.1,replaceBandConfiguration k (z.2.2,z.2.1))

lemma measurable_bandMeckeKernel (k : ℕ) (F : Point × CompleteWorld Seed → ℝ≥0∞)
    (hF : Measurable F) : Measurable (bandMeckeKernel k F) :=
  hF.comp (measurable_fst.prodMk ((measurable_replaceBandConfiguration k).comp
    ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))))

noncomputable def bandMeckeSum (k : ℕ) (F : Point × CompleteWorld Seed → ℝ≥0∞)
    (v : CompleteWorld Seed) : ℝ≥0∞ :=
  meckeSum (bandMeckeKernel k F) (v.1 k,v)

omit [MeasurableSpace Seed] in
lemma bandMeckeSum_eq (k : ℕ) (F : Point × CompleteWorld Seed → ℝ≥0∞) (v : CompleteWorld Seed) :
    bandMeckeSum k F v=∑ j : Fin (v.1 k).1, F ((v.1 k).2 j,eraseAnonymousPoint k v j) := rfl

lemma measurable_bandMeckeSum (k : ℕ) (F : Point × CompleteWorld Seed → ℝ≥0∞)
    (hF : Measurable F) : Measurable (bandMeckeSum k F) :=
  (measurable_meckeSum _ (measurable_bandMeckeKernel k F hF)).comp
    (((measurable_pi_apply k).comp measurable_fst).prodMk measurable_id)

omit [MeasurableSpace Seed] in
lemma bandMeckeSum_replace (k : ℕ) (F : Point × CompleteWorld Seed → ℝ≥0∞)
    (z : Configuration × CompleteWorld Seed) :
    bandMeckeSum k F (replaceBandConfiguration k (z.2,z.1))=meckeSum (bandMeckeKernel k F) z := by
  rcases z with ⟨q,v⟩
  have hConfig : (replaceBandConfiguration k (v,q)).1 k=q := Function.update_self _ _ _
  change meckeSum (bandMeckeKernel k F)
    ((replaceBandConfiguration k (v,q)).1 k,replaceBandConfiguration k (v,q))=meckeSum (bandMeckeKernel k F) (q,v)
  rw [hConfig]
  unfold meckeSum
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [bandMeckeKernel]
  rw [replaceBandConfiguration_idem]

theorem band_mecke (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (k : ℕ) (F : Point × CompleteWorld Seed → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, bandMeckeSum k F v ∂B.completeWorldLaw ν)=
      ∫⁻ z, F z ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν) := by
  have hSwap := Measure.measurePreserving_swap
    (μ := configurationLaw (B.bandIntensity k)) (ν := B.completeWorldLaw ν)
  have hReplace := (B.replaceBandConfiguration_measurePreserving k ν).comp hSwap
  have hLeft := hReplace.lintegral_comp (measurable_bandMeckeSum k F hF)
  have hRight := ((MeasurePreserving.id (ProphetSecretary.Limiting.intensity (B.bandIntensity k))).prod hReplace).lintegral_comp hF
  calc
    _ = ∫⁻ z : Configuration × CompleteWorld Seed, bandMeckeSum k F (replaceBandConfiguration k (z.2,z.1))
        ∂(configurationLaw (B.bandIntensity k)).prod (B.completeWorldLaw ν) := hLeft.symm
    _ = ∫⁻ z : Configuration × CompleteWorld Seed, meckeSum (bandMeckeKernel k F) z
        ∂(configurationLaw (B.bandIntensity k)).prod (B.completeWorldLaw ν) :=
      lintegral_congr_ae (Eventually.of_forall (bandMeckeSum_replace k F))
    _ = ∫⁻ z, bandMeckeKernel k F z
        ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (worldLaw (B.bandIntensity k) (B.completeWorldLaw ν)) :=
      mecke (B.bandIntensity k) (B.completeWorldLaw ν) _ (measurable_bandMeckeKernel k F hF)
    _ = _ := hRight

end ProphetSecretary.Limiting.CountableInstance
