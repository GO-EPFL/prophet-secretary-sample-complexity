import ProphetSecretary.Statistics.ReportedClockGrid
import ProphetSecretary.Model.ClockToRankLaw
import ProphetSecretary.Model.LawEndpointRegularity

/-!
# Rank profiles for the reported validation block

An independent permutation and sorted clock vector represent each
validation trajectory. The rank profile can be rounded before execution.
The prepared interpolation agrees almost surely with the continuous-clock
comparison model.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type}

abbrev RankValidationProfile (n J : ℕ) (PSeed : Type) :=
  (Fin n → ℝ) × (Equiv.Perm (Fin n) × ((Fin n → ℝ) × PolicyQueryArray n J PSeed))

def rankValidationProfileWorld (p : RankValidationProfile n J PSeed) :
    World n (PolicyQueryArray n J PSeed) :=
  (p.1,Instance.reconstructClocks (p.2.2.1,p.2.1),p.2.2.2)

def roundRankValidationProfile (f : ℝ → ℝ) (p : RankValidationProfile n J PSeed) :
    RankValidationProfile n J PSeed :=
  (p.1,p.2.1,f ∘ p.2.2.1,p.2.2.2)

noncomputable def rankValidationDuration [NeZero m] (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m PSeed) (q : Reservoir n m)
    (p : RankValidationProfile n J PSeed) (j : Fin (J+1)) : ℝ :=
  (frozenFamilyPolicy zlo zhi estimate q j).clockToRank.reportedDuration p.2.2 p.2.1 p.1 p.2.2.1

noncomputable def rankValidationPrepare [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (d : FirstInformation n m TSeed × (Fin m → RankValidationProfile n J PSeed)) : PreparedCalibration n m :=
  let q := reservoirCoordinates.symm d.1.1
  let ρ := computedTarget mu targetEstimate d.1.1 d.1.2
  (q,durationVectorSelection (rankValidationDuration zlo zhi policyEstimate q) d.2 ρ)

variable [MeasurableSpace PSeed]

noncomputable def rankValidationProfileLaw (P : Instance n) (νP : Measure PSeed) (times : Measure (Fin n → ℝ)) :
    Measure (RankValidationProfile n J PSeed) :=
  P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod (times.prod (policyQueryArrayLaw νP)))

instance rankValidationProfileLaw_probability (P : Instance n) (νP : Measure PSeed)
    (times : Measure (Fin n → ℝ)) [IsProbabilityMeasure νP] [IsProbabilityMeasure times] :
    IsProbabilityMeasure (rankValidationProfileLaw (J := J) P νP times) := by
  unfold rankValidationProfileLaw
  infer_instance

lemma rankValidationProfileWorld_measurePreserving (P : Instance n) (νP : Measure PSeed)
    [IsProbabilityMeasure νP] :
    MeasurePreserving (rankValidationProfileWorld (n := n) (J := J) (PSeed := PSeed))
      (rankValidationProfileLaw P νP (Instance.sortedTimesLaw n))
      (P.worldLaw (policyQueryArrayLaw νP)) := by
  let S := Instance.sortedTimesLaw n
  let U := Instance.uniformPermutationLaw n
  let R := policyQueryArrayLaw (n := n) (J := J) νP
  have h0 := (measurePreserving_prodAssoc U S R).symm MeasurableEquiv.prodAssoc
  have h1 := (Measure.measurePreserving_swap (μ := U) (ν := S)).prod (MeasurePreserving.id R)
  haveI : IsProbabilityMeasure ((Instance.clocksLaw n).map Instance.sortedClocks) :=
    Measure.isProbabilityMeasure_map Instance.measurable_sortedClocks.aemeasurable
  have h2 := (Instance.reconstructClocks_measurePreserving (n := n)).prod (MeasurePreserving.id R)
  exact (MeasurePreserving.id P.valuesLaw).prod (h2.comp (h1.comp h0))

lemma roundRankValidationProfile_measurePreserving (P : Instance n) (νP : Measure PSeed)
    [IsProbabilityMeasure νP] {f : ℝ → ℝ} (hf : Measurable f) :
    MeasurePreserving (roundRankValidationProfile (n := n) (J := J) (PSeed := PSeed) f)
      (rankValidationProfileLaw P νP (Instance.sortedTimesLaw n))
      (rankValidationProfileLaw P νP ((Instance.sortedTimesLaw n).map (fun s i => f (s i)))) := by
  have hM : Measurable (fun s : Fin n → ℝ => fun i => f (s i)) :=
    measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))
  have h : MeasurePreserving (fun s : Fin n → ℝ => fun i => f (s i)) (Instance.sortedTimesLaw n)
    ((Instance.sortedTimesLaw n).map (fun s i => f (s i))) := ⟨hM,rfl⟩
  exact (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod
    (h.prod (MeasurePreserving.id (policyQueryArrayLaw (n := n) (J := J) νP))))

lemma rankValidationProfile_times_regular (P : Instance n) (νP : Measure PSeed) [IsProbabilityMeasure νP] :
    ∀ᵐ p : RankValidationProfile n J PSeed ∂rankValidationProfileLaw P νP (Instance.sortedTimesLaw n),
      StrictMono p.2.2.1 ∧ ∀ k,p.2.2.1 k∈Ico (0 : ℝ) 1 := by
  let R := policyQueryArrayLaw (n := n) (J := J) νP
  let U := Instance.uniformPermutationLaw n
  let S := Instance.sortedTimesLaw n
  have hS : MeasurePreserving (fun p : RankValidationProfile n J PSeed => p.2.2.1)
      (rankValidationProfileLaw P νP S) S :=
    (measurePreserving_fst (μ := S) (ν := R)).comp
      ((measurePreserving_snd (μ := U) (ν := S.prod R)).comp
        (measurePreserving_snd (μ := P.valuesLaw) (ν := U.prod (S.prod R))))
  have hMap := rankValidationProfileWorld_measurePreserving (J := J) P νP
  filter_upwards [hS.quasiMeasurePreserving.ae (Instance.sortedTimesLaw_regular (n := n)),
    hMap.quasiMeasurePreserving.ae (P.world_clocks_mem_unitInterval R),
    hMap.quasiMeasurePreserving.ae (P.world_clocks_lt_one_ae R)] with p hStrict hU hLt
  refine ⟨hStrict.1,fun k => ?_⟩
  have hu := hU (p.2.1 k)
  have ht := hLt (p.2.1 k)
  simpa only [rankValidationProfileWorld,Instance.reconstructClocks,Equiv.symm_apply_apply] using
    (show (rankValidationProfileWorld p).2.1 (p.2.1 k)∈Ico (0 : ℝ) 1 from ⟨hu.1,ht⟩)

variable [MeasurableSpace TSeed] [NeZero m]

lemma rankValidationPrepare_eq_reported_ae (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    {zlo zhi : ℝ} (hz0 : 0≤zlo) (hz : zlo≤zhi)
    (f : ℝ → ℝ) (hf : ∀ t∈Icc (0 : ℝ) 1, f t∈Icc (0 : ℝ) t)
    (mu : ℝ) (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed) :
    ∀ᵐ d : FirstInformation n m TSeed × (Fin m → RankValidationProfile n J PSeed)
      ∂(firstInformationLaw P νT).prod (Measure.pi (fun _ => rankValidationProfileLaw P νP (Instance.sortedTimesLaw n))),
      rankValidationPrepare mu zlo zhi targetEstimate policyEstimate (d.1,fun i => roundRankValidationProfile f (d.2 i)) =
        reportedOfflinePrepare (terminalClockReport f) mu zlo zhi targetEstimate (clockRoundedEstimate f policyEstimate)
          (d.1,fun i => rankValidationProfileWorld (d.2 i)) := by
  let W := rankValidationProfileLaw (J := J) P νP (Instance.sortedTimesLaw n)
  let I := firstInformationLaw (m := m) P νT
  have hReg : ∀ᵐ d : FirstInformation n m TSeed × (Fin m → RankValidationProfile n J PSeed)
      ∂I.prod (Measure.pi (fun _ => W)),
      ∀ i : Fin m, StrictMono (d.2 i).2.2.1 ∧ ∀ k,(d.2 i).2.2.1 k∈Ico (0 : ℝ) 1 := by
    simp only [ae_all_iff]
    intro i
    have h := (measurePreserving_eval (fun _ : Fin m => W) i).comp
      (measurePreserving_snd (μ := I) (ν := Measure.pi (fun _ : Fin m => W)))
    exact h.quasiMeasurePreserving.ae (rankValidationProfile_times_regular (J := J) P νP)
  filter_upwards [hReg] with d hd
  let q := reservoirCoordinates.symm d.1.1
  let ρ := computedTarget mu targetEstimate d.1.1 d.1.2
  let τ := rankValidationDuration (J := J) zlo zhi policyEstimate q
  let σ := reportedValidationDuration (J := J) (terminalClockReport f) zlo zhi
    (clockRoundedEstimate f policyEstimate) q
  have he (i : Fin m) : τ (roundRankValidationProfile f (d.2 i))=σ (rankValidationProfileWorld (d.2 i)) := by
    funext j
    exact (reportedValidationDuration_eq_rank hz0 hz f hf policyEstimate q j
      (d.2 i).2.2.2 (d.2 i).2.2.1 (hd i).1 (hd i).2 (d.2 i).2.1 (d.2 i).1).symm
  have hV : durationVectorAverage τ (fun i => roundRankValidationProfile f (d.2 i)) =
      durationVectorAverage σ (fun i => rankValidationProfileWorld (d.2 i)) := by
    funext k
    unfold durationVectorAverage
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [he i]
  change (q,durationVectorSelection τ (fun i => roundRankValidationProfile f (d.2 i)) ρ) =
    (q,durationVectorSelection σ (fun i => rankValidationProfileWorld (d.2 i)) ρ)
  simp only [durationVectorSelection,hV]

end ProphetSecretary.Statistics.Calibration
