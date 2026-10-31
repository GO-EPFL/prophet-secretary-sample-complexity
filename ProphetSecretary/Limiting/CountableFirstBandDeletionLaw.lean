import ProphetSecretary.Limiting.CountableFirstBandWindow
import ProphetSecretary.Limiting.CountableObservations
import ProphetSecretary.Limiting.ZeroIntensity
import Mathlib.Probability.ProductMeasure

/-!
# Actual deletion of a finite prefix of Poisson construction bands

The existing zero band-scaling constructor gives a valid countable instance.
The corresponding complete-world map replaces exactly the deleted finite
arrays by the empty configuration. Its full product pushforward is proved
coordinatewise, leaving every individual identity, value, clock and seed
unchanged. No ordering or future count is disclosed to a policy.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

noncomputable def deleteFirstBands (B : CountableInstance) (N : ℕ) : CountableInstance :=
  B.scaleBand (B.firstBandWindow N) 0

lemma deleteFirstBands_bandIntensity (B : CountableInstance) (N k : ℕ) :
    (B.deleteFirstBands N).bandIntensity k=if k≤N then 0 else B.bandIntensity k :=
  B.scaleBand_firstBandWindow_bandIntensity N k

noncomputable def eraseFirstBandConfigurations (N : ℕ) (ω : BandConfigurations) : BandConfigurations :=
  fun k => if k≤N then emptyConfiguration else ω k

noncomputable def eraseFirstBandsWorld (N : ℕ) (v : CompleteWorld Seed) : CompleteWorld Seed :=
  (eraseFirstBandConfigurations N v.1,v.2)

lemma measurable_eraseFirstBandConfigurations (N : ℕ) : Measurable (eraseFirstBandConfigurations N) := by
  apply measurable_pi_lambda
  intro k
  by_cases hk : k≤N
  · simpa only [eraseFirstBandConfigurations,if_pos hk] using
      (measurable_const : Measurable (fun _ : BandConfigurations => emptyConfiguration))
  · simpa only [eraseFirstBandConfigurations,if_neg hk] using (measurable_pi_apply k : Measurable (fun ω : BandConfigurations => ω k))

theorem eraseFirstBandConfigurations_measurePreserving (B : CountableInstance) (N : ℕ) :
    MeasurePreserving (eraseFirstBandConfigurations N) B.bandConfigurationsLaw (B.deleteFirstBands N).bandConfigurationsLaw := by
  let f : ℕ → Configuration → Configuration := fun k q => if k≤N then emptyConfiguration else q
  have hf (k : ℕ) : Measurable (f k) := by
    by_cases hk : k≤N
    · simpa only [f,if_pos hk] using (measurable_const : Measurable (fun _ : Configuration => emptyConfiguration))
    · simp only [f,if_neg hk]
      exact measurable_id
  refine ⟨measurable_eraseFirstBandConfigurations N,?_⟩
  change Measure.map (fun ω k => f k (ω k)) (Measure.infinitePi (fun k => configurationLaw (B.bandIntensity k)))=
    Measure.infinitePi (fun k => configurationLaw ((B.deleteFirstBands N).bandIntensity k))
  rw [Measure.infinitePi_map_pi _ hf]
  congr 1
  funext k
  rw [B.deleteFirstBands_bandIntensity]
  by_cases hk : k≤N
  · simp only [f,if_pos hk,configurationLaw_zero,Measure.map_const,measure_univ,one_smul]
  · simp only [f,if_neg hk]
    exact Measure.map_id

variable [MeasurableSpace Seed]

lemma measurable_eraseFirstBandsWorld (N : ℕ) : Measurable (eraseFirstBandsWorld (Seed := Seed) N) :=
  ((measurable_eraseFirstBandConfigurations N).comp measurable_fst).prodMk measurable_snd

theorem eraseFirstBandsWorld_measurePreserving (B : CountableInstance) (N : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (eraseFirstBandsWorld N) (B.completeWorldLaw ν)
      ((B.deleteFirstBands N).completeWorldLaw ν) :=
  (B.eraseFirstBandConfigurations_measurePreserving N).prod (MeasurePreserving.id (B.individualWorldLaw ν))

end ProphetSecretary.Limiting.CountableInstance
