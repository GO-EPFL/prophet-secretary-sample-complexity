import ProphetSecretary.Statistics.PremiumMean
import ProphetSecretary.Model.SingleIdentity
import ProphetSecretary.Model.FirstArrivalIntegral
import ProphetSecretary.Model.ScalarCoefficientMeasurability

/-!
# First-arrival recursion for unstopped premiums

The full positive-premium sum splits into the first marginal premium and the same sum
on the actual remaining instance with its rescaled duration coefficient. These are
pathwise identities on the derived first-arrival execution, before taking moments.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.clockPremium_first (Q : Instance (n + 1)) (w c : ℝ)
    (i : Fin (n + 1)) {t : ℝ} (ht : t < 1)
    (v : Fin (remainingSet i).card → ℝ) (hv : ∀ j, 0 < v j) :
    Q.clockPremium w c (Instance.firstChildClocks i (t, v)) i =
      positivePremium (Q.law i) w (Q.bellmanContinuation i w c t) := by
  unfold Instance.clockPremium
  rw [Q.continuationAtArrival_values_invariant w c (fun _ => 0) (insertCandidate i (0, fun _ => 0))
    (Instance.firstChildClocks i (t, v)) i,
    Q.continuationAtArrival_first w c i ht 0 (fun _ => 0) v hv]

lemma Instance.clockPremium_extend (Q : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (A : Finset (Fin n)) {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (v : Fin A.card → ℝ)
    (j : Fin A.card) (hv : 0 < v j) :
    Q.clockPremium w c (extendClocks A s H v) (stateEmbedding A j) =
      (Q.restrictTo A).clockPremium w (c * (1 - s)) v j := by
  have h := Q.transitionResidual_extend (zeroInstance n) hQ A hs H hH hw hc (fun _ => 0) v j hv
  rw [Q.transitionResidual_zero hQ hw.le hc, zeroInstance_restrictTo,
    (Q.restrictTo A).transitionResidual_zero (Q.restrictTo_integrable_maximum A hQ) hw.le
      (mul_nonneg hc (sub_nonneg.mpr hs.le))] at h
  exact h

lemma Instance.unstoppedPremium_firstStep (Q : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin (n + 1)) {t : ℝ} (ht : t < 1)
    (v : Fin (remainingSet i).card → ℝ) (hv : ∀ j, 0 < v j) :
    Q.unstoppedPremium w c (Instance.firstChildClocks i (t, v)) =
      positivePremium (Q.law i) w (Q.bellmanContinuation i w c t) +
        (Q.restrictTo (remainingSet i)).unstoppedPremium w (c * (1 - t)) v := by
  let F : Fin (n + 1) → ℝ := fun j => Q.clockPremium w c (Instance.firstChildClocks i (t, v)) j
  have hfirst : F i = positivePremium (Q.law i) w (Q.bellmanContinuation i w c t) :=
    Q.clockPremium_first w c i ht v hv
  change (∑ j, F j) = _
  rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ i), hfirst]
  apply congrArg (positivePremium (Q.law i) w (Q.bellmanContinuation i w c t) + ·)
  have hmap : Finset.univ.map (stateEmbedding (remainingSet i)) = remainingSet i :=
    (remainingSet i).map_orderEmbOfFin_univ rfl
  change (∑ j ∈ remainingSet i, F j) = _
  rw (occs := .pos [1]) [← hmap]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j _
  have h := Q.clockPremium_extend hQ (remainingSet i) ht (firstPrefix i t 0)
    (validPrefix_firstPrefix i t 0) hw hc v j (hv j)
  rw [extendClocks_firstPrefix] at h
  exact h

lemma Instance.bellmanContinuation_le_initialValue (Q : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c t : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (ht : 0 ≤ t) (i : Fin (n + 1)) :
    Q.bellmanContinuation i w c t ≤ optimalScalarValue Q w c := by
  have h := Q.valueThreshold_le_initialValue hQ hw hc ht Finset.univ i
  change Q.bellmanContinuation i w c t / w ≤ optimalScalarValue Q w c / w at h
  exact (div_le_div_iff_of_pos_right hw).mp h

lemma Instance.firstPremium_le_initialValue (Q : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (t : ℝ) (i : Fin (n + 1)) :
    positivePremium (Q.law i) w (Q.bellmanContinuation i w c t) ≤ optimalScalarValue Q w c := by
  have hθ : 0 ≤ Q.bellmanContinuation i w c t :=
    optimalScalarValue_nonnegative (Q.restrictTo (remainingSet i)) (Q.restrictTo_integrable_maximum _ hQ)
      hw.le (mul_nonneg hc (le_max_left _ _))
  exact (positivePremium_le_firstMoment (Q.law i) (Q.integrable_maximum_iff.mp hQ i) (Q.nonnegative i) hw.le hθ).trans
    (optimalScalarValue_ge_coordinateMean Q hQ hw.le hc i)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The coefficient may vary jointly with every clock coordinate. -/
lemma Instance.measurable_unstoppedPremium_durationCoeff (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w : ℝ} (hw : 0 < w)
    {c : Ω → ℝ} {u : Ω → Fin n → ℝ} (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hu : ∀ j, Measurable fun ω => u ω j) :
    Measurable fun ω => Q.unstoppedPremium w (c ω) (u ω) := by
  have hstate (i : Fin n) : Measurable (fun ω => (unseen (history Finset.univ (fun _ => 0) (u ω) (u ω i))).erase i) :=
    (measurable_of_finite (fun A : Finset (Fin n) => A.erase i)).comp
      (measurable_unseen.comp (measurable_history Finset.univ (fun _ => measurable_const) hu (hu i)))
  apply Finset.measurable_sum
  intro i _
  have hfixed (A : Finset (Fin n)) : Measurable (fun ω =>
      optimalScalarValue (Q.restrictTo A) w (c ω * max 0 (1 - u ω i))) :=
    (Q.restrictTo A).measurable_scalarValue_coefficients (Q.restrictTo_integrable_maximum A hQ)
      measurable_const (hc.mul (measurable_const.max (measurable_const.sub (hu i))))
      (fun _ => hw.le) (fun ω => mul_nonneg (hc0 ω) (le_max_left _ _))
  have hchoice : Measurable (fun z : Finset (Fin n) × Ω =>
      optimalScalarValue (Q.restrictTo z.1) w (c z.2 * max 0 (1 - u z.2 i))) :=
    measurable_from_prod_countable_right hfixed
  have hθ := hchoice.comp ((hstate i).prodMk measurable_id)
  exact (positivePremium_continuous (Q.law i) (Q.integrable_maximum_iff.mp hQ i) w).measurable.comp hθ

end ProphetSecretary.Model
