import ProphetSecretary.Statistics.MixedEmpiricalEnvelopeIncrementMoments
import ProphetSecretary.Statistics.EmpiricalEnvelopeProcess

/-!
# Actual mixed scalar envelope on an affine interval

The process retains the complete sample and clock dependencies. Joint
measurability, path continuity, common-event finite bounds and uniform moment
increments follow from the constructed mixed-law residuals. The generic
increment constant is unchanged and independent of known identities.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def Instance.mixedIntervalEnvelope (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k]
    (lo hi : ℝ) (v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : ℝ :=
  (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 (max 0 (lo + (hi - lo) * t)) v.2

variable {k : ℕ} [NeZero k]

theorem Instance.mixedEnvelopeDifference_moment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {p : ℕ} (hp : p = 2 ∨ p = 6)
    {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    (∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 -
       (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z' v.2| ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalIncrementMomentConstant k p * |z' - z| ^ p := by
  apply ProphetSecretary.Statistics.increment_moment_bound_of_ordered
    (by rcases hp with rfl | rfl <;> decide) _ (s := z) (t := z') (hs := hz) (ht := hz')
  intro s t hs hst
  rcases hp with rfl | rfl
  · simpa [empiricalIncrementMomentConstant] using P.mixedEnvelopeDifference_secondMoment (k := k) known hbound hs hst
  · simpa [empiricalIncrementMomentConstant] using P.mixedEnvelopeDifference_sixthMoment (k := k) known hbound hs hst

lemma Instance.measurable_mixedIntervalEnvelope (P : Instance n) (known : Finset (Fin n))
    (hP : Integrable Instance.maximum P.valuesLaw) (lo hi t : ℝ) :
    Measurable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => P.mixedIntervalEnvelope known k lo hi v t) :=
  P.measurable_mixedResidualSuffixEnvelope hP known
    (y := fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => reservoirCoordinates.symm v.1)
    (c := fun _ => max 0 (lo + (hi - lo) * t)) (u := Prod.snd)
    (fun i j => (measurable_pi_apply (i, j)).comp measurable_fst) measurable_const
    (fun _ => le_max_left _ _) (fun i => (measurable_pi_apply i).comp measurable_snd)

lemma Instance.continuous_mixedIntervalEnvelope (P : Instance n) (known : Finset (Fin n))
    (hP : Integrable Instance.maximum P.valuesLaw) (lo hi : ℝ)
    (v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    Continuous (P.mixedIntervalEnvelope known k lo hi v) :=
  ((mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).continuous_clampedResidualSuffixEnvelope P
    (mixedEmpiricalInstance_integrable P hP known _) hP v.2).comp
    (continuous_const.add (continuous_const.mul continuous_id))

lemma Instance.mixedIntervalEnvelope_bounded (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (lo hi : ℝ) :
    ∀ᵐ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ t : ℝ, |P.mixedIntervalEnvelope known k lo hi v t| ≤ n := by
  have hv : MeasurePreserving (Prod.fst : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ((Fin n × Fin k) → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (P.trainingCoordinateLaw k) := measurePreserving_fst
  filter_upwards [hv.quasiMeasurePreserving.ae (trainingCoordinates_unit_ae P hbound)] with v hv
  intro t
  have h0 : 0 ≤ P.mixedIntervalEnvelope known k lo hi v t := ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
  rw [abs_of_nonneg h0]
  exact P.mixedResidualSuffixEnvelope_le_card hbound known (reservoirCoordinates.symm v.1) hv (le_max_left _ _) v.2

/-- Actual uniform increment input for dyadic chaining, valid on every affine
scalar interval and with constants independent of the number of distributions. -/
theorem Instance.mixedIntervalEnvelope_increment_moment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {p : ℕ} (hp : p = 2 ∨ p = 6)
    (lo hi s t : ℝ) :
    (∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
      |P.mixedIntervalEnvelope known k lo hi v s - P.mixedIntervalEnvelope known k lo hi v t| ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      (empiricalIncrementMomentConstant k p * |hi - lo| ^ p) * |t - s| ^ p := by
  have h := P.mixedEnvelopeDifference_moment (k := k) known hbound hp
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
