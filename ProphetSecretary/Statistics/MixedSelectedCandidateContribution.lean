import ProphetSecretary.Statistics.MixedClockLossDirection
import ProphetSecretary.Statistics.TrainingScalarFreeze
import ProphetSecretary.Statistics.MixedDataSelectedClockLossIntegrability

/-!
# Both actual mixed candidate contributions with a selected scalar

The full array and independent seed select one scalar, fixed during candidate
time integration. Both directions integrate the independent TRUE candidate law.
Joint measurability, common auxiliary bounds and exact inverse row splitting
are proved before using their statistical rate.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Seed : Type*} [MeasurableSpace Seed]

noncomputable def mixedOtherCandidateLossMean (P : Instance n) (known : Finset (Fin n))
    (a : (Fin n × Fin k) → ℝ) (z : ℝ) (reverse : Bool) (i : Fin n)
    (v : Fin (Finset.univ.erase i).card → ℝ) : ℝ :=
  ∫ x, (∫ t, mixedClockGapLossDirection (P.restrictTo (Finset.univ.erase i))
    (knownInState known (Finset.univ.erase i))
    (reservoirCoordinates.symm (restrictTrainingCoordinates (Finset.univ.erase i) a)) z reverse v x t
      ∂Instance.uniformClock) ∂P.law i

noncomputable def mixedSelectedCandidateContribution (P : Instance n) (known : Finset (Fin n)) (Z : Reservoir n k × Seed → ℝ)
    (reverse : Bool) (i : Fin n) (p : (((Fin n × Fin k) → ℝ) × Seed)) : ℝ :=
  ∫ v, mixedOtherCandidateLossMean P known p.1 (Z (reservoirCoordinates.symm p.1,p.2)) reverse i v
    ∂Instance.clocksLaw (Finset.univ.erase i).card

lemma measurable_mixedSelectedCandidateContribution (P : Instance n) (known : Finset (Fin n))
    (hP : Integrable Instance.maximum P.valuesLaw) {Z : Reservoir n k × Seed → ℝ}
    (hZ : Measurable Z) (hZ0 : ∀ p, 0≤Z p) (reverse : Bool) (i : Fin n) : Measurable (mixedSelectedCandidateContribution P known Z reverse i) := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  let D := ((Fin n × Fin k) → ℝ) × Seed
  let T := ((D × (Fin A.card → ℝ)) × ℝ) × ℝ
  have hy (j : Fin A.card) (l : Fin k) : Measurable (fun ω : T =>
      reservoirCoordinates.symm (restrictTrainingCoordinates A ω.1.1.1.1) j l) :=
    (measurable_pi_apply (stateEmbedding A j,l)).comp (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
  have hz : Measurable (fun ω : T => Z (reservoirCoordinates.symm ω.1.1.1.1,ω.1.1.1.2)) :=
    hZ.comp (((reservoirCoordinates.symm.measurable).comp
      (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))).prodMk
      (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))))
  have hu (j : Fin A.card) : Measurable (fun ω : T => ω.1.1.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hL : Measurable (fun ω : T => mixedClockGapLossDirection (P.restrictTo A) (knownInState known A)
      (reservoirCoordinates.symm (restrictTrainingCoordinates A ω.1.1.1.1))
      (Z (reservoirCoordinates.symm ω.1.1.1.1,ω.1.1.1.2)) reverse ω.1.1.2 ω.1.2 ω.2) :=
    measurable_mixedClockGapLossDirection (P.restrictTo A) (P.restrictTo_integrable_maximum A hP) (knownInState known A)
      hy hz measurable_snd (measurable_snd.comp measurable_fst) hu (fun ω => hZ0 _) reverse
  have hT : Measurable (fun ω : (D × (Fin A.card → ℝ)) × ℝ =>
      ∫ t, mixedClockGapLossDirection (P.restrictTo A) (knownInState known A)
        (reservoirCoordinates.symm (restrictTrainingCoordinates A ω.1.1.1))
        (Z (reservoirCoordinates.symm ω.1.1.1,ω.1.1.2)) reverse ω.1.2 ω.2 t ∂Instance.uniformClock) :=
    (hL.stronglyMeasurable.integral_prod_right' (ν:=Instance.uniformClock)).measurable
  have hX : Measurable (fun ω : D × (Fin A.card → ℝ) =>
      ∫ x, (∫ t, mixedClockGapLossDirection (P.restrictTo A) (knownInState known A)
        (reservoirCoordinates.symm (restrictTrainingCoordinates A ω.1.1))
        (Z (reservoirCoordinates.symm ω.1.1,ω.1.2)) reverse ω.2 x t ∂Instance.uniformClock) ∂P.law i) :=
    (hT.stronglyMeasurable.integral_prod_right' (ν:=P.law i)).measurable
  exact (hX.stronglyMeasurable.integral_prod_right' (ν:=Instance.clocksLaw A.card)).measurable

omit [MeasurableSpace Seed] in
lemma mixedSelectedCandidateContribution_nonnegative (P : Instance n) (known : Finset (Fin n)) (Z : Reservoir n k × Seed → ℝ)
    (reverse : Bool) (i : Fin n) (p : (((Fin n × Fin k) → ℝ) × Seed)) : 0≤mixedSelectedCandidateContribution P known Z reverse i p := by
  apply integral_nonneg
  intro v
  apply integral_nonneg
  intro x
  apply integral_nonneg
  intro t
  exact mixedClockGapLossDirection_nonnegative _ _ _ _ _ _ _ _

/-- The inverse row split reconstructs both the own-row-dependent scalar and
all other rows exactly; this is a pointwise identity, not merely a law equality. -/
lemma mixedSelectedCandidateContribution_merge (P : Instance n) (known : Finset (Fin n)) (Z : Reservoir n k × Seed → ℝ) (reverse : Bool) (i : Fin n)
    (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) (r : (Fin k → ℝ) × Seed) :
    mixedSelectedCandidateContribution P known Z reverse i ((splitTrainingRowSeedEquiv i).symm (b,r)) =
      ∫ v, (∫ x, (∫ t, mixedClockGapLossDirection (P.restrictTo (Finset.univ.erase i)) (knownInState known (Finset.univ.erase i)) (reservoirCoordinates.symm b)
        (frozenOtherScalar Z i r b) reverse v x t ∂Instance.uniformClock) ∂P.law i)
        ∂Instance.clocksLaw (Finset.univ.erase i).card := by
  change (∫ v, mixedOtherCandidateLossMean P known ((splitTrainingRowEquiv i).symm (b,r.1))
    (frozenOtherScalar Z i r b) reverse i v ∂Instance.clocksLaw (Finset.univ.erase i).card) = _
  unfold mixedOtherCandidateLossMean
  rw [restrictTrainingCoordinates_merge]

omit [MeasurableSpace Seed] in
lemma mixedSelectedCandidateContribution_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : Reservoir n k × Seed → ℝ} {hi : ℝ}
    (hZ : ∀ p, Z p ∈ Icc (0:ℝ) hi) (reverse : Bool) (i : Fin n)
    (p : (((Fin n × Fin k) → ℝ) × Seed)) (ha : ∀ j l, p.1 (j,l)≤1) :
    mixedSelectedCandidateContribution P known Z reverse i p ≤ 2+2*hi := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  let Q := P.restrictTo A
  let y := reservoirCoordinates.symm (restrictTrainingCoordinates A p.1)
  let z := Z (reservoirCoordinates.symm p.1,p.2)
  have hQ : ∀ j, ∀ᵐ x ∂Q.law j, x≤1 := fun j => hbound (stateEmbedding A j)
  have hy : ∀ j l, y j l≤1 := fun j l => ha (stateEmbedding A j) l
  have hz : z∈Icc (0:ℝ) hi := hZ _
  have hT (v : Fin A.card → ℝ) (x : ℝ) :
      ‖∫ t, mixedClockGapLossDirection Q (knownInState known A) y z reverse v x t ∂Instance.uniformClock‖≤2+2*hi := by
    have h := norm_integral_le_of_norm_le_const (μ:=Instance.uniformClock)
      (C:=2+2*hi) (f:=fun t => mixedClockGapLossDirection Q (knownInState known A) y z reverse v x t) ?_
    · simpa using h
    filter_upwards [uniformClock_nonnegative_ae] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (mixedClockGapLossDirection_nonnegative _ _ _ _ _ _ _ _)]
    exact mixedClockGapLossDirection_bounded Q (knownInState known A) hQ y hy hz.1 hz.2 ht reverse v x
  have hX (v : Fin A.card → ℝ) :
      ‖∫ x, (∫ t, mixedClockGapLossDirection Q (knownInState known A) y z reverse v x t ∂Instance.uniformClock) ∂P.law i‖≤2+2*hi := by
    simpa using norm_integral_le_of_norm_le_const (μ:=P.law i) (Eventually.of_forall (hT v))
  have h := norm_integral_le_of_norm_le_const (μ:=Instance.clocksLaw A.card) (Eventually.of_forall hX)
  have he : ‖mixedSelectedCandidateContribution P known Z reverse i p‖≤2+2*hi := by
    simpa only [mixedSelectedCandidateContribution,mixedOtherCandidateLossMean,
      probReal_univ,mul_one] using h
  exact le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using he)

lemma integrable_mixedSelectedCandidateContribution (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : Reservoir n k × Seed → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ p, Z p∈Icc (0:ℝ) hi) (reverse : Bool) (i : Fin n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    Integrable (mixedSelectedCandidateContribution P known Z reverse i) ((P.trainingCoordinateLaw k).prod ν) := by
  apply Integrable.of_bound (measurable_mixedSelectedCandidateContribution P known
    (P.integrable_maximum_of_bounded hbound) hZ (fun p => (hZrange p).1) reverse i).aestronglyMeasurable (2+2*hi)
  have ha := (measurePreserving_fst (μ:=P.trainingCoordinateLaw k) (ν:=ν)).quasiMeasurePreserving.ae
    (P.trainingCoordinates_bounded (k:=k) hbound)
  filter_upwards [ha] with p hp
  rw [Real.norm_eq_abs,abs_of_nonneg (mixedSelectedCandidateContribution_nonnegative _ _ _ _ _ _)]
  exact mixedSelectedCandidateContribution_le P known hbound hZrange reverse i p hp

end ProphetSecretary.Model
