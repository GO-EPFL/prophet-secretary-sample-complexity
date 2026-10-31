import ProphetSecretary.Statistics.MixedClockLossBounds

/-!
# Actual mixed clock losses at a training-selected scalar

The scalar depends on training coordinates and remains fixed while candidate
time is integrated. Joint sample/value/clock/time measurability and a common
auxiliary bound justify all later product-law interchanges. Known marginal
laws are exact at their fixed declared identities.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def mixedDataSelectedClockLoss (P : Instance n) (known : Finset (Fin n)) (Z : ((Fin n × Fin k) → ℝ) → ℝ)
    (x : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : ℝ :=
  mixedClockGapLoss P known (reservoirCoordinates.symm q.1) (Z q.1) q.2 x t

noncomputable def mixedDataSelectedClockLossReverse (P : Instance n) (known : Finset (Fin n)) (Z : ((Fin n × Fin k) → ℝ) → ℝ)
    (x : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : ℝ :=
  trueClockGapLossMixedEval P known (reservoirCoordinates.symm q.1) (Z q.1) q.2 x t

theorem measurable_mixedDataSelectedClockLoss_pair (P : Instance n) (known : Finset (Fin n))
    (hP : Integrable Instance.maximum P.valuesLaw) {Z : ((Fin n × Fin k) → ℝ) → ℝ}
    (hZ : Measurable Z) (hZ0 : ∀ a, 0≤Z a) (x : ℝ) :
    Measurable (fun q : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) => mixedDataSelectedClockLoss P known Z x q.1 q.2) ∧
      Measurable (fun q : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) => mixedDataSelectedClockLossReverse P known Z x q.1 q.2) := by
  have hy (j : Fin n) (l : Fin k) : Measurable
      (fun q : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) => reservoirCoordinates.symm q.1.1 j l) :=
    (measurable_pi_apply (j,l)).comp (measurable_fst.comp measurable_fst)
  have hz : Measurable (fun q : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) => Z q.1.1) :=
    hZ.comp (measurable_fst.comp measurable_fst)
  have hu (j : Fin n) : Measurable (fun q : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) => q.1.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)
  exact ⟨measurable_mixedClockGapLoss P hP known hy hz measurable_snd measurable_const hu (fun q => hZ0 q.1.1),
    measurable_trueClockGapLossMixedEval P hP known hy hz measurable_snd measurable_const hu (fun q => hZ0 q.1.1)⟩

/-- Joint candidate-value measurability needed before integrating its marginal
law; the internal error envelopes need not be made jointly measurable in x. -/
theorem measurable_mixedDataSelectedClockLoss_pair_jointValue (P : Instance n) (known : Finset (Fin n))
    (hP : Integrable Instance.maximum P.valuesLaw) {Z : ((Fin n × Fin k) → ℝ) → ℝ}
    (hZ : Measurable Z) (hZ0 : ∀ a, 0≤Z a) :
    Measurable (fun q : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) => mixedDataSelectedClockLoss P known Z q.1.2 q.1.1 q.2) ∧
      Measurable (fun q : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) => mixedDataSelectedClockLossReverse P known Z q.1.2 q.1.1 q.2) := by
  have hy (j : Fin n) (l : Fin k) : Measurable
      (fun q : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) => reservoirCoordinates.symm q.1.1.1 j l) :=
    (measurable_pi_apply (j,l)).comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have hz : Measurable (fun q : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) => Z q.1.1.1) :=
    hZ.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have hu (j : Fin n) : Measurable (fun q : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) => q.1.1.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
  exact ⟨measurable_mixedClockGapLoss P hP known hy hz measurable_snd (measurable_snd.comp measurable_fst) hu (fun q => hZ0 q.1.1.1),
    measurable_trueClockGapLossMixedEval P hP known hy hz measurable_snd (measurable_snd.comp measurable_fst) hu (fun q => hZ0 q.1.1.1)⟩

lemma mixedDataSelectedClockLoss_nonnegative (P : Instance n) (known : Finset (Fin n)) (Z : ((Fin n × Fin k) → ℝ) → ℝ)
    (x : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : 0≤mixedDataSelectedClockLoss P known Z x q t :=
  mixedClockGapLoss_nonnegative _ _ _ _ _ _ _

lemma mixedDataSelectedClockLossReverse_nonnegative (P : Instance n) (known : Finset (Fin n)) (Z : ((Fin n × Fin k) → ℝ) → ℝ)
    (x : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : 0≤mixedDataSelectedClockLossReverse P known Z x q t :=
  trueClockGapLossMixedEval_nonnegative _ _ _ _ _ _ _

/-- The same sample event supports every independent auxiliary freeze and every
candidate value. This bound is used only to justify integration. -/
theorem Instance.mixedDataSelectedClockLoss_pair_bounded (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi : ℝ}
    (hZ : ∀ a, Z a∈Icc (0:ℝ) hi) (x : ℝ) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k, ∀ u : Fin n → ℝ, ∀ t : ℝ, 0≤t →
      mixedDataSelectedClockLoss P known Z x (a,u) t≤2+2*hi ∧ mixedDataSelectedClockLossReverse P known Z x (a,u) t≤2+2*hi := by
  filter_upwards [P.paired_mixedClockGapLoss_bounded_ae (k:=k) known hbound hi] with a ha
  exact fun u t ht => ha (Z a) (hZ a) u x t ht

end ProphetSecretary.Model
