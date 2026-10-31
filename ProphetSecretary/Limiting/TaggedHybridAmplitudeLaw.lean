import ProphetSecretary.Limiting.TaggedHybridAmplitude
import ProphetSecretary.Limiting.HybridSelectedTag

/-!
# Selected amplitudes on the actual tagged-policy law

The analytical payload coefficient equals the selected tag of the ordinary
policy driven by independent chronological tags. Equality uses only the
finite prefix corresponding to actual anonymous arrivals.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed T : Type*} [MeasurableSpace T]

noncomputable def chronologicalAmplitudeTag (A : ℝ × T → ℝ) : HybridTags n (Seed × (ℕ → T)) :=
  fun v k => Fin.addCases (fun _ : Fin n => 0) (fun j : Fin v.1.1 =>
    A ((v.1.2 j).2,v.2.2.2.2 (Model.Instance.arrivalRank (fun l : Fin v.1.1 => (v.1.2 l).1) j).val)) k

lemma TaggedHybridRule.payloadSelectedAmplitude_assigned (π : TaggedHybridRule n Seed T)
    (t0 : T) (A : ℝ × T → ℝ) (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) (seq : ℕ → T)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) :
    π.payloadSelectedAmplitude t0 A
        (chronologicalPayloadConfiguration (id : ℝ × T → ℝ × T) (ω,seq),(x,(u,r)))=
      (π.sampleTags.asFinitePolicy ω.1).selectedTag (r,seq)
        (combinedValues x ω.2) (combinedClocks u ω.2)
        (chronologicalAmplitudeTag A (ω,(x,(u,(r,seq))))) := by
  let seq2 := payloadTagSequence t0 (chronologicalPayloadConfiguration (id : ℝ × T → ℝ × T) (ω,seq))
  have ha := π.sampleTags_actions_eq_of_prefix r x u ω seq2 seq hClock
    (payloadTagSequence_assigned_prefix t0 ω seq)
  have hSelect (k : Fin (n+ω.1)) :
      (π.sampleTags.asFinitePolicy ω.1).ActualSelects (r,seq2) Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) k ↔
      (π.sampleTags.asFinitePolicy ω.1).ActualSelects (r,seq) Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) k := by
    constructor
    · exact (π.sampleTags.asFinitePolicy ω.1).actualSelects_of_subexecution
        (π.sampleTags.asFinitePolicy ω.1) (OrderIso.refl _).toOrderEmbedding (r,seq2) (r,seq)
        (combinedValues x ω.2) (combinedClocks u ω.2) (combinedValues x ω.2) (combinedClocks u ω.2)
        (fun _ => rfl) (fun j => (ha j).symm) k
    · exact (π.sampleTags.asFinitePolicy ω.1).actualSelects_of_subexecution
        (π.sampleTags.asFinitePolicy ω.1) (OrderIso.refl _).toOrderEmbedding (r,seq) (r,seq2)
        (combinedValues x ω.2) (combinedClocks u ω.2) (combinedValues x ω.2) (combinedClocks u ω.2)
        (fun _ => rfl) ha k
  change (π.sampleTags.asFinitePolicy ω.1).selectedTag (r,seq2)
    (combinedValues x ω.2) (combinedClocks u ω.2)
    (fun k => Fin.addCases (fun _ : Fin n => 0) (fun j : Fin ω.1 => A ((ω.2 j).2,
      seq (Model.Instance.arrivalRank (fun l : Fin ω.1 => (ω.2 l).1) j).val)) k)=_
  unfold Model.Policy.selectedTag
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (π.sampleTags.asFinitePolicy ω.1).ActualSelects (r,seq) Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) k
  · rw [if_pos hk,if_pos ((hSelect k).mpr hk)]
    rfl
  · rw [if_neg hk,if_neg (fun h => hk ((hSelect k).mp h))]

variable [MeasurableSpace Seed]

lemma chronologicalAmplitudeTag_isMeasurable (A : ℝ × T → ℝ) (hA : Measurable A) :
    (chronologicalAmplitudeTag (n := n) (Seed := Seed) A).IsMeasurable := by
  intro N k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [chronologicalAmplitudeTag,configurationMk,Fin.addCases_left]
    exact measurable_const
  · simp only [chronologicalAmplitudeTag,configurationMk,Fin.addCases_right]
    let Ω := (Fin N → Point) × Model.World n (Seed × (ℕ → T))
    have hClocks : Measurable (fun z : Ω => fun l : Fin N => (z.1 l).1) :=
      measurable_pi_lambda _ (fun l => ((measurable_pi_apply l).comp measurable_fst).fst)
    have hRank : Measurable (fun z : Ω => (Model.Instance.arrivalRank (fun l : Fin N => (z.1 l).1) j).val) :=
      (measurable_of_countable (fun p : Equiv.Perm (Fin N) => (p.symm j).val)).comp
        (Model.Instance.measurable_arrivalPermutation.comp hClocks)
    have hEval : Measurable (fun z : (ℕ → T) × ℕ => z.1 z.2) :=
      measurable_from_prod_countable_left (fun l => measurable_pi_apply l)
    simpa only [Function.comp_def] using hA.comp ((((measurable_pi_apply j).comp measurable_fst).snd).prodMk
      (hEval.comp (measurable_snd.snd.snd.snd.prodMk hRank)))

lemma TaggedHybridRule.integral_payloadSelectedAmplitude_eq (π : TaggedHybridRule n Seed T)
    (hπ : π.IsMeasurable) (B : FiniteIntensityHybridInstance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (κ : Measure T) [IsProbabilityMeasure κ]
    (t0 : T) (A : ℝ × T → ℝ) (hA : Measurable A) :
    (∫ v, π.payloadSelectedAmplitude t0 A v ∂taggedHybridWorldLaw B ν κ)=
      ∫ v, (π.sampleTags.asFinitePolicy v.1.1).selectedTag v.2.2.2
        (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) (chronologicalAmplitudeTag A v)
        ∂B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ))) := by
  have hMP := sampledTaggedHybridWorld_measurePreserving B ν κ
  rw [← hMP.hasLaw.integral_comp (π.measurable_payloadSelectedAmplitude hπ t0 A hA).aestronglyMeasurable]
  apply integral_congr_ae
  have hCfg : MeasurePreserving (Prod.fst : HybridWorld n (Seed × (ℕ → T)) → Configuration)
      (B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ)))) (configurationLaw B.intensity) := measurePreserving_fst
  filter_upwards [hCfg.quasiMeasurePreserving.ae (configuration_times_distinct B.intensity)] with v hv
  exact π.payloadSelectedAmplitude_assigned t0 A v.2.2.2.1 v.2.1 v.2.2.1 v.1 v.2.2.2.2 hv

end ProphetSecretary.Limiting
