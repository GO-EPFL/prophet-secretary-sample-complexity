import ProphetSecretary.Statistics.EmpiricalCapAcceptance

/-!
# Cap acceptance for almost-surely bounded selected scalars

An almost-sure interval constraint is totalized by clipping the selected
scalar, so the actual modified learner accepts caps, rejects zero and obeys
the hard budget on every training outcome. The clipped scalar agrees almost
surely with the original one; the expected loss is measured against the
original empirical learner and uses that same original scalar.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

noncomputable def capAcceptanceScalar {Seed : Type*} (lo : ℝ)
    (Z : Reservoir n k × Seed → ℝ) : Reservoir n k × Seed → ℝ :=
  fun p => max lo (min (1/4) (Z p))

private lemma selected_frozen_scalar_eq_of_scalar_eq (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (Z T : Reservoir n k × Seed → ℝ) (hZ : Measurable Z) (hT : Measurable T)
    (y : Reservoir n k) (r : Seed) (hZT : Z (y,r) = T (y,r)) (P : Instance n) (w c : ℝ) :
    ((Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ).frozenRandomizedPolicy y r).scalarObjective P w c =
      ((Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) T measurable_const hT).frozenRandomizedPolicy y r).scalarObjective P w c := by
  let K := Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ
  let L := Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) T measurable_const hT
  have hdec : (K.frozenRule y r).decide = (L.frozenRule y r).decide := by
    funext s t i x H
    change (Learner.ofSamplePolicy Seed ν (empiricalSelectedPolicy (fun _ => 1) Z)
      (empiricalSelectedPolicy_isMeasurable measurable_const hZ)).policy.decide (y,r) t i x H =
        (Learner.ofSamplePolicy Seed ν (empiricalSelectedPolicy (fun _ => 1) T)
      (empiricalSelectedPolicy_isMeasurable measurable_const hT)).policy.decide (y,r) t i x H
    rw [Learner.ofSamplePolicy_decide,Learner.ofSamplePolicy_decide]
    change decide (empiricalValueThreshold y 1 (Z (y,r)) (unseen H) t i ≤ x) =
      decide (empiricalValueThreshold y 1 (T (y,r)) (unseen H) t i ≤ x)
    rw [hZT]
  have hRule : K.frozenRule y r = L.frozenRule y r := congrArg Policy.mk hdec
  change (∫ ω : World n Unit, w*(K.frozenRule y r).reward ω.2.2 Finset.univ ω.1 ω.2.1 +
    c*(K.frozenRule y r).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ())) =
      (∫ ω : World n Unit, w*(L.frozenRule y r).reward ω.2.2 Finset.univ ω.1 ω.2.1 +
    c*(L.frozenRule y r).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ()))
  rw [hRule]

/-- `lem:empirical-cap-acceptance`, with actual learners and explicit universal
cost. Scalar totalization affects only a null training set, while the policy
and budget conclusions have no exceptional training outcomes. -/
theorem Learner.empirical_cap_acceptance_ae (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z)
    {lo : ℝ} (hlo : 0 < lo) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (hM : P.expectedMaximum ≤ 1/80)
    (hRange : ∀ᵐ p ∂(P.reservoirLaw k).prod ν, Z p ∈ Icc lo (1/4 : ℝ)) :
    ∃ (T : Reservoir n k × Seed → ℝ) (hT : Measurable T),
      T = capAcceptanceScalar lo Z ∧ (∀ p, T p ∈ Icc lo (1/4 : ℝ)) ∧ T =ᵐ[(P.reservoirLaw k).prod ν] Z ∧
      let L := Learner.empiricalCapAcceptance Seed ν T hT
      let K := Learner.empiricalWithSelectedWeights Seed ν (fun _ => 1) Z measurable_const hZ
      (∀ (y : Reservoir n k) (r : Seed) (i : Fin n), requests (trainingTranscript L.request r y) i ≤ k) ∧
      (∀ y r t i H, 0 ≤ t → L.policy.decide (y,r) t i 1 H = true) ∧
      (∀ y r t i H, L.policy.decide (y,r) t i 0 H = false) ∧
      MonotoneThresholds (fun p A t i => empiricalCapThreshold p.1 (T p) A t i) ∧
      (∫ p, (K.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)-
        (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p) ∂(P.reservoirLaw k).prod ν) ≤
        (100/361 : ℝ)/(k : ℝ) := by
  have hlohi : lo ≤ (1/4 : ℝ) := by
    obtain ⟨p,hp⟩ := hRange.exists
    exact hp.1.trans hp.2
  let T : Reservoir n k × Seed → ℝ := capAcceptanceScalar lo Z
  have hT : Measurable T := measurable_const.max (measurable_const.min hZ)
  have hTrange (p : Reservoir n k × Seed) : T p ∈ Icc lo (1/4 : ℝ) :=
    ⟨le_max_left _ _,max_le hlohi (min_le_left _ _)⟩
  have hEq : T =ᵐ[(P.reservoirLaw k).prod ν] Z := by
    filter_upwards [hRange] with p hp
    exact (congrArg (max lo) (min_eq_right hp.2)).trans (max_eq_right hp.1)
  refine ⟨T,hT,rfl,hTrange,hEq,?_,?_,?_,empiricalCapThresholds_monotone T,?_⟩
  · exact Learner.empiricalCapAcceptance_hardBudget Seed ν T hT
  · intro y r t i H ht
    exact Learner.empiricalCapAcceptance_accepts_one Seed ν T hT y r ht
      (hlo.le.trans (hTrange (y,r)).1) (hTrange (y,r)).2 i H
  · exact Learner.empiricalCapAcceptance_rejects_zero Seed ν T hT
  · have hb := Learner.empiricalCapAcceptance_expected_loss_le_const Seed ν T hT hlo
      (fun p => (hTrange p).1) (fun p => (hTrange p).2) P hcap hM
    apply le_trans _ hb
    apply le_of_eq
    apply integral_congr_ae
    filter_upwards [hEq] with p hp
    have hK := selected_frozen_scalar_eq_of_scalar_eq Seed ν Z T hZ hT p.1 p.2 hp.symm P 1 (Z p)
    rw [hK,hp]

end ProphetSecretary.Model
