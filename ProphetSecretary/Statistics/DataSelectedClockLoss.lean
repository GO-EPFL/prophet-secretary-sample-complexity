import ProphetSecretary.Statistics.EmpiricalClockLossBounds

/-!
# Actual time losses with a training-selected scalar

The scalar is a function of the training coordinates only. An independent
auxiliary input can be held fixed before forming this function, as in
`TrainingScalarFreeze`. Thus time integration keeps the coefficient fixed,
while joint measurability and a uniform auxiliary bound justify later Fubini.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def dataSelectedClockLoss (P : Instance n) (Z : ((Fin n × Fin k) → ℝ) → ℝ)
    (x : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : ℝ :=
  empiricalClockGapLoss P (reservoirCoordinates.symm q.1) (Z q.1) q.2 x t

noncomputable def dataSelectedClockLossReverse (P : Instance n) (Z : ((Fin n × Fin k) → ℝ) → ℝ)
    (x : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : ℝ :=
  trueClockGapLossEmpiricalEval P (reservoirCoordinates.symm q.1) (Z q.1) q.2 x t

theorem measurable_dataSelectedClockLoss_pair (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {Z : ((Fin n × Fin k) → ℝ) → ℝ}
    (hZ : Measurable Z) (hZ0 : ∀ a, 0≤Z a) (x : ℝ) :
    Measurable (fun q : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) => dataSelectedClockLoss P Z x q.1 q.2) ∧
      Measurable (fun q : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) => dataSelectedClockLossReverse P Z x q.1 q.2) := by
  have hy (j : Fin n) (l : Fin k) : Measurable
      (fun q : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) => reservoirCoordinates.symm q.1.1 j l) :=
    (measurable_pi_apply (j,l)).comp (measurable_fst.comp measurable_fst)
  have hz : Measurable (fun q : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) => Z q.1.1) :=
    hZ.comp (measurable_fst.comp measurable_fst)
  have hu (j : Fin n) : Measurable (fun q : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) => q.1.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)
  exact ⟨measurable_empiricalClockGapLoss P hP hy hz measurable_snd measurable_const hu (fun q => hZ0 q.1.1),
    measurable_trueClockGapLossEmpiricalEval P hP hy hz measurable_snd measurable_const hu (fun q => hZ0 q.1.1)⟩

/-- Joint candidate-value measurability needed before integrating its marginal
law; the internal error envelopes need not be made jointly measurable in x. -/
theorem measurable_dataSelectedClockLoss_pair_jointValue (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {Z : ((Fin n × Fin k) → ℝ) → ℝ}
    (hZ : Measurable Z) (hZ0 : ∀ a, 0≤Z a) :
    Measurable (fun q : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) => dataSelectedClockLoss P Z q.1.2 q.1.1 q.2) ∧
      Measurable (fun q : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) => dataSelectedClockLossReverse P Z q.1.2 q.1.1 q.2) := by
  have hy (j : Fin n) (l : Fin k) : Measurable
      (fun q : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) => reservoirCoordinates.symm q.1.1.1 j l) :=
    (measurable_pi_apply (j,l)).comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have hz : Measurable (fun q : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) => Z q.1.1.1) :=
    hZ.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have hu (j : Fin n) : Measurable (fun q : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) => q.1.1.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
  exact ⟨measurable_empiricalClockGapLoss P hP hy hz measurable_snd (measurable_snd.comp measurable_fst) hu (fun q => hZ0 q.1.1.1),
    measurable_trueClockGapLossEmpiricalEval P hP hy hz measurable_snd (measurable_snd.comp measurable_fst) hu (fun q => hZ0 q.1.1.1)⟩

lemma dataSelectedClockLoss_nonnegative (P : Instance n) (Z : ((Fin n × Fin k) → ℝ) → ℝ)
    (x : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : 0≤dataSelectedClockLoss P Z x q t :=
  empiricalClockGapLoss_nonnegative _ _ _ _ _ _

lemma dataSelectedClockLossReverse_nonnegative (P : Instance n) (Z : ((Fin n × Fin k) → ℝ) → ℝ)
    (x : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : 0≤dataSelectedClockLossReverse P Z x q t :=
  trueClockGapLossEmpiricalEval_nonnegative _ _ _ _ _ _

/-- The same sample event supports every independent auxiliary freeze and every
candidate value. This bound is used only to justify integration. -/
theorem Instance.dataSelectedClockLoss_pair_bounded (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi : ℝ}
    (hZ : ∀ a, Z a∈Icc (0:ℝ) hi) (x : ℝ) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k, ∀ u : Fin n → ℝ, ∀ t : ℝ, 0≤t →
      dataSelectedClockLoss P Z x (a,u) t≤2+2*hi ∧ dataSelectedClockLossReverse P Z x (a,u) t≤2+2*hi := by
  filter_upwards [P.paired_clockGapLoss_bounded_ae (k:=k) hbound hi] with a ha
  exact fun u t ht => ha (Z a) (hZ a) u x t ht

end ProphetSecretary.Model
