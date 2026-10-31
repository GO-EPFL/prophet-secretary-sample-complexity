import ProphetSecretary.Model.EmpiricalTotalization
import ProphetSecretary.Model.BellmanOptimal

/-!
# Joint measurability of empirical scalar values

The optimal scalar value is the supremum over all admissible policies. Its empirical
parameter measurability is proved from the established finite Bellman equation, by
induction on the number of identities. Empirical transitions are finite sample averages;
only integration against a fixed first-arrival time measure remains.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

lemma totalEmpiricalInstance_bellman {n k : ℕ} [NeZero k] (y : Reservoir (n + 1) k)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue (totalEmpiricalInstance y) w c =
      ∑ i : Fin (n + 1), ∫ t,
        (k : ℝ)⁻¹ * ∑ j : Fin k,
          (c * t + max (w * max 0 (y i j))
            ((totalEmpiricalInstance y).bellmanContinuation i w c t))
        ∂Instance.firstChildTimeLaw i := by
  let P := totalEmpiricalInstance y
  have hP := totalEmpiricalInstance_integrable y
  rw [P.optimalScalarValue_eq_bellmanValue hP hw hc]
  unfold Instance.bellmanValue
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_prod _ (P.integrable_bellmanFirstPayoff hP i hw.le hc)]
  apply integral_congr_ae
  filter_upwards [] with t
  exact totalEmpiricalInstance_integral y i (fun x => P.bellmanFirstPayoff i w c (t, x))

/-- Joint empirical-array and coefficient measurability, derived without a policy
selection theorem or an assumed measurable supremum. Reward weight is positive and
duration weight nonnegative at every parameter; later a.e. restrictions can be totalized. -/
theorem measurable_optimalScalarValue_totalEmpirical
    {n k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]
    {y : Ω → Reservoir n k} {w c : Ω → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hw : Measurable w) (hc : Measurable c)
    (hw0 : ∀ ω, 0 < w ω) (hc0 : ∀ ω, 0 ≤ c ω) :
    Measurable fun ω => optimalScalarValue (totalEmpiricalInstance (y ω)) (w ω) (c ω) := by
  induction n using Nat.strong_induction_on generalizing Ω with
  | h n ih =>
    cases n with
    | zero =>
      simpa only [optimalScalarValue_empty] using hc
    | succ n =>
      have hterm (i : Fin (n + 1)) : Measurable fun ω : Ω => ∫ t,
          (k : ℝ)⁻¹ * ∑ j : Fin k,
            (c ω * t + max (w ω * max 0 (y ω i j))
              ((totalEmpiricalInstance (y ω)).bellmanContinuation i (w ω) (c ω) t))
          ∂Instance.firstChildTimeLaw i := by
        have hcard : (remainingSet i).card < n + 1 := by simp [remainingSet]
        have hchild := ih (remainingSet i).card hcard
          (Ω := Ω × ℝ)
          (y := fun z j l => y z.1 (stateEmbedding (remainingSet i) j) l)
          (w := fun z => w z.1)
          (c := fun z => c z.1 * max 0 (1 - z.2))
          (fun j l => (hy _ l).comp measurable_fst)
          (hw.comp measurable_fst)
          ((hc.comp measurable_fst).mul (measurable_const.max (measurable_const.sub measurable_snd)))
          (fun z => hw0 z.1) (fun z => mul_nonneg (hc0 z.1) (le_max_left _ _))
        have hcont : Measurable (fun z : Ω × ℝ =>
            (totalEmpiricalInstance (y z.1)).bellmanContinuation i (w z.1) (c z.1) z.2) := by
          simpa only [Instance.bellmanContinuation, totalEmpiricalInstance_restrictTo] using hchild
        have hf : Measurable (fun z : Ω × ℝ =>
            (k : ℝ)⁻¹ * ∑ j : Fin k,
              (c z.1 * z.2 + max (w z.1 * max 0 (y z.1 i j))
                ((totalEmpiricalInstance (y z.1)).bellmanContinuation i (w z.1) (c z.1) z.2))) := by
          apply Measurable.const_mul
          apply Finset.measurable_sum
          intro j _
          exact ((hc.comp measurable_fst).mul measurable_snd).add
            (((hw.comp measurable_fst).mul (measurable_const.max ((hy i j).comp measurable_fst))).max hcont)
        exact hf.stronglyMeasurable.integral_prod_right'.measurable
      have hsum : Measurable fun ω : Ω => ∑ i : Fin (n + 1), ∫ t,
          (k : ℝ)⁻¹ * ∑ j : Fin k,
            (c ω * t + max (w ω * max 0 (y ω i j))
              ((totalEmpiricalInstance (y ω)).bellmanContinuation i (w ω) (c ω) t))
          ∂Instance.firstChildTimeLaw i := Finset.measurable_sum _ (fun i _ => hterm i)
      convert hsum using 1
      funext ω
      exact totalEmpiricalInstance_bellman (y ω) (hw0 ω) (hc0 ω)

end ProphetSecretary.Model
