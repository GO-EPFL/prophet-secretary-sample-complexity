import ProphetSecretary.Statistics.EmpiricalEnvelopeIncrementMoments

/-!
# The actual scalar empirical envelope process

The process is indexed by an affine scalar interval and is totalized outside the
nonnegative coefficient domain by clamping. Joint sample/clock measurability,
path continuity, a finite integrability bound, and uniform increment moments are
all derived from the actual finite-instance construction.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Statistics

variable {Ω : Type*} [MeasurableSpace Ω]

lemma increment_moment_bound_of_ordered {μ : Measure Ω} {f : ℝ → Ω → ℝ} {p : ℕ}
    (hp : 0 < p) (B : ℝ)
    (hOrdered : ∀ {s t : ℝ}, 0 ≤ s → s < t →
      (∫ ω, |f s ω - f t ω| ^ p ∂μ) ≤ B * (t - s) ^ p)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫ ω, |f s ω - f t ω| ^ p ∂μ) ≤ B * |t - s| ^ p := by
  rcases lt_trichotomy s t with h | h | h
  · simpa only [abs_of_nonneg (sub_nonneg.mpr h.le)] using hOrdered hs h
  · subst t
    simp only [sub_self, abs_zero, zero_pow (Nat.ne_of_gt hp), integral_zero, mul_zero, le_refl]
  · calc
      _ = ∫ ω, |f t ω - f s ω| ^ p ∂μ := by congr 1; funext ω; rw [abs_sub_comm]
      _ ≤ B * (s - t) ^ p := hOrdered ht h
      _ = _ := by rw [abs_of_nonpos (sub_nonpos.mpr h.le), neg_sub]

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def empiricalIncrementMomentConstant (k p : ℕ) : ℝ :=
  if p = 2 then 4 / (k : ℝ) else (106000000000 ^ 2 + 212000000000) / (k : ℝ) ^ 3

lemma empiricalIncrementMomentConstant_nonnegative (k p : ℕ) : 0 ≤ empiricalIncrementMomentConstant k p := by
  unfold empiricalIncrementMomentConstant
  split_ifs <;> positivity

noncomputable def Instance.empiricalIntervalEnvelope (P : Instance n) (k : ℕ) [NeZero k]
    (lo hi : ℝ) (v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : ℝ :=
  (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 (max 0 (lo + (hi - lo) * t)) v.2

variable {k : ℕ} [NeZero k]

theorem Instance.empiricalEnvelopeDifference_moment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {p : ℕ} (hp : p = 2 ∨ p = 6)
    {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    (∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
      |(totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 -
       (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z' v.2| ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalIncrementMomentConstant k p * |z' - z| ^ p := by
  apply ProphetSecretary.Statistics.increment_moment_bound_of_ordered
    (by rcases hp with rfl | rfl <;> decide) _ (s := z) (t := z') (hs := hz) (ht := hz')
  intro s t hs hst
  rcases hp with rfl | rfl
  · simpa [empiricalIncrementMomentConstant] using P.empiricalEnvelopeDifference_secondMoment (k := k) hbound hs hst
  · simpa [empiricalIncrementMomentConstant] using P.empiricalEnvelopeDifference_sixthMoment (k := k) hbound hs hst

lemma Instance.measurable_empiricalIntervalEnvelope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (lo hi t : ℝ) :
    Measurable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => P.empiricalIntervalEnvelope k lo hi v t) :=
  P.measurable_empiricalResidualSuffixEnvelope hP
    (y := fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => reservoirCoordinates.symm v.1)
    (c := fun _ => max 0 (lo + (hi - lo) * t)) (u := Prod.snd)
    (fun i j => (measurable_pi_apply (i, j)).comp measurable_fst) measurable_const
    (fun _ => le_max_left _ _) (fun i => (measurable_pi_apply i).comp measurable_snd)

lemma Instance.continuous_empiricalIntervalEnvelope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (lo hi : ℝ)
    (v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    Continuous (P.empiricalIntervalEnvelope k lo hi v) :=
  ((totalEmpiricalInstance (reservoirCoordinates.symm v.1)).continuous_clampedResidualSuffixEnvelope P
    (totalEmpiricalInstance_integrable _) hP v.2).comp
    (continuous_const.add (continuous_const.mul continuous_id))

lemma Instance.empiricalIntervalEnvelope_bounded (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (lo hi : ℝ) :
    ∀ᵐ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ t : ℝ, |P.empiricalIntervalEnvelope k lo hi v t| ≤ n := by
  have hv : MeasurePreserving (Prod.fst : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ((Fin n × Fin k) → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (P.trainingCoordinateLaw k) := measurePreserving_fst
  filter_upwards [hv.quasiMeasurePreserving.ae (trainingCoordinates_unit_ae P hbound)] with v hv
  intro t
  have h0 : 0 ≤ P.empiricalIntervalEnvelope k lo hi v t := ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
  rw [abs_of_nonneg h0]
  exact P.empiricalResidualSuffixEnvelope_le_card hbound (reservoirCoordinates.symm v.1) hv (le_max_left _ _) v.2

/-- Actual uniform increment input for dyadic chaining, valid on every affine
scalar interval and with constants independent of the number of distributions. -/
theorem Instance.empiricalIntervalEnvelope_increment_moment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {p : ℕ} (hp : p = 2 ∨ p = 6)
    (lo hi s t : ℝ) :
    (∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
      |P.empiricalIntervalEnvelope k lo hi v s - P.empiricalIntervalEnvelope k lo hi v t| ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      (empiricalIncrementMomentConstant k p * |hi - lo| ^ p) * |t - s| ^ p := by
  have h := P.empiricalEnvelopeDifference_moment (k := k) hbound hp
    (le_max_left (0 : ℝ) (lo + (hi - lo) * s)) (le_max_left (0 : ℝ) (lo + (hi - lo) * t))
  have hmax : |max 0 (lo + (hi - lo) * t) - max 0 (lo + (hi - lo) * s)| ≤ |hi - lo| * |t - s| := by
    have hm := abs_max_sub_max_le_abs (lo + (hi - lo) * t) (lo + (hi - lo) * s) (0 : ℝ)
    calc
      _ ≤ |(lo + (hi - lo) * t) - (lo + (hi - lo) * s)| := by simpa only [max_comm] using hm
      _ = _ := by rw [← abs_mul]; congr 1; ring

  apply h.trans
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hmax p)
    (empiricalIncrementMomentConstant_nonnegative k p)).trans_eq (by rw [mul_pow]; ring)

end ProphetSecretary.Model
