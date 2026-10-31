import ProphetSecretary.Limiting.CountableIndividualSplit
import ProphetSecretary.Limiting.FiniteMeasurePast
import ProphetSecretary.Probability.FiniteMeasureTotalization

/-!
# Causal reconstruction of omitted observations from auxiliary data

Retained history entries, including observed zeros, are left intact. Virtual
individuals contribute exactly their strict past. A locally finite omitted
cloud is reconstructed band by band, so joint measurability does not assume
that an arbitrary infinite random measure has a finite total count.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def augmentIndividualHistory (N : ℕ) (H : Model.History N) (zX zU : ℕ → ℝ)
    (t : ℝ) : IndividualHistory := fun i =>
  if hi : i < N then H ⟨i,hi⟩ else individualHistory zX zU t (i-N)

lemma measurable_augmentIndividualHistory {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {H : Ω → Model.History N} {zX zU : Ω → ℕ → ℝ} {t : Ω → ℝ}
    (hH : Measurable H) (hX : Measurable zX) (hU : Measurable zU) (ht : Measurable t) :
    Measurable (fun ω => augmentIndividualHistory N (H ω) (zX ω) (zU ω) (t ω)) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i < N
  · simp only [augmentIndividualHistory,dif_pos hi]
    exact (measurable_pi_apply (⟨i,hi⟩ : Fin N)).comp hH
  · simp only [augmentIndividualHistory,dif_neg hi]
    exact (measurable_pi_apply (i-N)).comp (measurable_individualHistory
      (fun j => (measurable_pi_apply j).comp hX) (fun j => (measurable_pi_apply j).comp hU) ht)

lemma augmentIndividualHistory_actual {N : ℕ} (x u : Fin N → ℝ) (zX zU : ℕ → ℝ) (t : ℝ) :
    augmentIndividualHistory N (Model.history Finset.univ x u t) zX zU t =
      individualHistory (splicePrefix x zX) (splicePrefix u zU) t := by
  funext i
  by_cases hi : i < N
  · simp only [augmentIndividualHistory,individualHistory,splicePrefix,dif_pos hi,
      Model.history,Finset.mem_univ,true_and]
  · simp only [augmentIndividualHistory,individualHistory,splicePrefix,dif_neg hi]

noncomputable def omittedCloudPast (B : CountableInstance) (μ : Measure Point) (t : ℝ) : Measure Point :=
  Measure.sum (fun k => finitePast
    (ProphetSecretary.Probability.finiteMeasureOrZero (μ.restrict (univ ×ˢ B.markBand k))) t)

lemma measurable_omittedCloudPast (B : CountableInstance) :
    Measurable (fun q : Measure Point × ℝ => omittedCloudPast B q.1 q.2) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have he : (fun q : Measure Point × ℝ => omittedCloudPast B q.1 q.2 S) =
      fun q => ∑' k, finitePast (ProphetSecretary.Probability.finiteMeasureOrZero
        (q.1.restrict (univ ×ˢ B.markBand k))) q.2 S := by
    funext q
    exact Measure.sum_apply _ hS
  rw [he]
  apply Measurable.tsum
  intro k
  have hμ : Measurable (fun q : Measure Point × ℝ => ProphetSecretary.Probability.finiteMeasureOrZero
      (q.1.restrict (univ ×ˢ B.markBand k))) :=
    ProphetSecretary.Probability.measurable_finiteMeasureOrZero.comp
      ((measurable_measureRestriction (MeasurableSet.univ.prod (B.measurableSet_markBand k))).comp measurable_fst)
  exact (Measure.measurable_coe hS).comp (measurable_finitePast.comp (hμ.prodMk measurable_snd))

lemma measurable_omittedCloudPast_family (B : CountableInstance) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Ω → Measure Point} {t : Ω → ℝ} (hμ : Measurable μ) (ht : Measurable t) :
    Measurable (fun ω => omittedCloudPast B (μ ω) (t ω)) := by
  have hm := (measurable_omittedCloudPast B).comp (hμ.prodMk ht)
  change Measurable (fun ω => omittedCloudPast B (μ ω) (t ω)) at hm
  exact hm

lemma omittedCloudPast_eq (B : CountableInstance) (μ : Measure Point)
    (hsupport : ∀ᵐ p ∂μ, (B.terminal : ℝ) < p.2)
    (hfinite : ∀ k, IsFiniteMeasure (μ.restrict (univ ×ˢ B.markBand k))) (t : ℝ) :
    omittedCloudPast B μ t = μ.restrict (Iio t ×ˢ univ) := by
  have hDisj : Pairwise (fun k l => Disjoint ((univ : Set ℝ) ×ˢ B.markBand k) ((univ : Set ℝ) ×ˢ B.markBand l)) := by
    intro k l hkl
    exact Set.disjoint_left.mpr (fun _ hp hq => Set.disjoint_left.mp (B.markBands_disjoint hkl) hp.2 hq.2)
  have hUnion : (⋃ k, (univ ×ˢ B.markBand k : Set Point)) = univ ×ˢ Ioi (B.terminal : ℝ) := by
    rw [← Set.prod_iUnion,B.iUnion_markBand]
  have hSum : Measure.sum (fun k => μ.restrict (univ ×ˢ B.markBand k)) = μ := by
    rw [← Measure.restrict_iUnion hDisj (fun k => MeasurableSet.univ.prod (B.measurableSet_markBand k)),hUnion]
    apply Measure.restrict_eq_self_of_ae_mem
    exact hsupport.mono (fun _ hp => ⟨Set.mem_univ _,hp⟩)
  calc
    _ = Measure.sum (fun k => (μ.restrict (univ ×ˢ B.markBand k)).restrict (Iio t ×ˢ univ)) := by
      apply congrArg Measure.sum
      funext k
      rw [finitePast,ProphetSecretary.Probability.finiteMeasureOrZero_coe _ (hfinite k)]
    _ = (Measure.sum (fun k => μ.restrict (univ ×ˢ B.markBand k))).restrict (Iio t ×ˢ univ) :=
      (Measure.restrict_sum _ (measurableSet_Iio.prod MeasurableSet.univ)).symm
    _ = _ := congrArg (fun ν : Measure Point => ν.restrict (Iio t ×ˢ univ)) hSum

end ProphetSecretary.Limiting.CountableInstance
