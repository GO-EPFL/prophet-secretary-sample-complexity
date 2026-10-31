import ProphetSecretary.Limiting.CountableAppendPoint
import ProphetSecretary.Probability.InfiniteCoordinateReplacement

/-!
# Fresh replacement of an actual Poisson construction band

An independent configuration with the band's own law replaces that band,
retaining every other band, individual value, clock and independent policy
seed. Infinite-product replacement and product regrouping prove the actual
full-world pushforward used to lift the finite Mecke identity.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

def replaceBandConfiguration (k : ℕ) (z : CompleteWorld Seed × Configuration) : CompleteWorld Seed :=
  (Function.update z.1.1 k z.2,z.1.2)

lemma replaceBandConfiguration_self (k : ℕ) (v : CompleteWorld Seed) :
    replaceBandConfiguration k (v,v.1 k)=v := by
  unfold replaceBandConfiguration
  rw [Function.update_eq_self]

lemma replaceBandConfiguration_idem (k : ℕ) (v : CompleteWorld Seed) (q r : Configuration) :
    replaceBandConfiguration k (replaceBandConfiguration k (v,q),r)=replaceBandConfiguration k (v,r) := by
  simp only [replaceBandConfiguration,Function.update_idem]

lemma appendAnonymousPoint_replaceBandConfiguration (k : ℕ) (v : CompleteWorld Seed)
    (q : Configuration) (p : Point) :
    appendAnonymousPoint k p (replaceBandConfiguration k (v,q))=
      replaceBandConfiguration k (v,appendConfigurationPoint q p) := by
  simp only [appendAnonymousPoint,replaceBandConfiguration,Function.update_self,Function.update_idem]

variable [MeasurableSpace Seed]

theorem replaceBandConfiguration_measurePreserving (B : CountableInstance) (k : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (replaceBandConfiguration k)
      ((B.completeWorldLaw ν).prod (configurationLaw (B.bandIntensity k))) (B.completeWorldLaw ν) := by
  have hReplace := ProphetSecretary.Probability.infinite_replaceCoordinate_measurePreserving
    (fun j => configurationLaw (B.bandIntensity j)) k
  have hSwap := Model.measurePreserving_swap_last B.bandConfigurationsLaw
    (B.individualWorldLaw ν) (configurationLaw (B.bandIntensity k))
  exact (hReplace.prod (MeasurePreserving.id (B.individualWorldLaw ν))).comp hSwap

lemma measurable_replaceBandConfiguration (k : ℕ) :
    Measurable (replaceBandConfiguration (Seed := Seed) k) := by
  have hCloud : Measurable (fun z : CompleteWorld Seed × Configuration => Function.update z.1.1 k z.2) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j=k
    · subst j
      simpa only [Function.update_self] using
        (measurable_snd : Measurable (fun z : CompleteWorld Seed × Configuration => z.2))
    · simpa only [Function.update_of_ne hj,Function.comp_def] using
        (measurable_pi_apply j).comp (measurable_fst.comp
          (measurable_fst : Measurable (fun z : CompleteWorld Seed × Configuration => z.1)))
  exact hCloud.prodMk (measurable_snd.comp measurable_fst)

end ProphetSecretary.Limiting.CountableInstance
