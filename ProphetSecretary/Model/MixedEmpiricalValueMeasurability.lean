import ProphetSecretary.Model.MixedEmpiricalInstance
import ProphetSecretary.Model.BellmanOptimal

/-!
# Measurable scalar values with exact known marginals

Finite Bellman induction handles each known marginal by integration against its
fixed law, and each unknown marginal by its literal finite sample average.
This proves joint measurability without assuming a measurable optimal-policy
selection, and retains the unrestricted admissible-policy optimal value.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

/-- Known true laws and all remaining sample entries may coexist in the same
canonical continuation. The true known laws need only finite first moments. -/
theorem measurable_optimalScalarValue_mixedEmpirical
    {n k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {w c : Ω → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hw : Measurable w) (hc : Measurable c)
    (hw0 : ∀ ω, 0<w ω) (hc0 : ∀ ω, 0≤c ω) :
    Measurable fun ω => optimalScalarValue (mixedEmpiricalInstance P known (y ω)) (w ω) (c ω) := by
  induction n using Nat.strong_induction_on generalizing Ω with
  | h n ih =>
    cases n with
    | zero => simpa only [optimalScalarValue_empty] using hc
    | succ n =>
      let Q := fun ω => mixedEmpiricalInstance P known (y ω)
      have hterm (i : Fin (n+1)) : Measurable (fun ω : Ω => ∫ t,
          (∫ x, (Q ω).bellmanFirstPayoff i (w ω) (c ω) (t,x) ∂(Q ω).law i)
          ∂Instance.firstChildTimeLaw i) := by
        have hcard : (remainingSet i).card<n+1 := by simp [remainingSet]
        have hchild := ih (remainingSet i).card hcard
          (Ω:=Ω×ℝ) (P.restrictTo (remainingSet i)) (P.restrictTo_integrable_maximum _ hP)
          (knownInState known (remainingSet i))
          (y:=fun z j l => y z.1 (stateEmbedding (remainingSet i) j) l)
          (w:=fun z => w z.1) (c:=fun z => c z.1*max 0 (1-z.2))
          (fun j l => (hy _ l).comp measurable_fst) (hw.comp measurable_fst)
          ((hc.comp measurable_fst).mul (measurable_const.max (measurable_const.sub measurable_snd)))
          (fun z => hw0 z.1) (fun z => mul_nonneg (hc0 z.1) (le_max_left _ _))
        have hcont : Measurable (fun z : Ω×ℝ => (Q z.1).bellmanContinuation i (w z.1) (c z.1) z.2) := by
          simpa only [Q,Instance.bellmanContinuation,mixedEmpiricalInstance_restrictTo] using hchild
        by_cases hi : i∈known
        · have hf : Measurable (fun z : (Ω×ℝ)×ℝ =>
              c z.1.1*z.1.2+max (w z.1.1*z.2) ((Q z.1.1).bellmanContinuation i (w z.1.1) (c z.1.1) z.1.2)) :=
            (((hc.comp measurable_fst).comp measurable_fst).mul (measurable_snd.comp measurable_fst)).add
              ((((hw.comp measurable_fst).comp measurable_fst).mul measurable_snd).max (hcont.comp measurable_fst))
          have hm := (hf.stronglyMeasurable.integral_prod_right' (ν:=P.law i)).integral_prod_right'
            (ν:=Instance.firstChildTimeLaw i)
          convert hm.measurable using 1
          funext ω
          rw [mixedEmpiricalInstance_law_known P known (y ω) hi]
          rfl
        · have hf : Measurable (fun z : Ω×ℝ => (k:ℝ)⁻¹*∑ l : Fin k,
              (c z.1*z.2+max (w z.1*max 0 (y z.1 i l))
                ((Q z.1).bellmanContinuation i (w z.1) (c z.1) z.2))) := by
            apply Measurable.const_mul
            apply Finset.measurable_sum
            intro l _
            exact ((hc.comp measurable_fst).mul measurable_snd).add
              (((hw.comp measurable_fst).mul (measurable_const.max ((hy i l).comp measurable_fst))).max hcont)
          have hm := (hf.stronglyMeasurable.integral_prod_right' (ν:=Instance.firstChildTimeLaw i)).measurable
          convert hm using 1
          funext ω
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t =>
            mixedEmpiricalInstance_integral_unknown P known (y ω) hi
              (fun x => (Q ω).bellmanFirstPayoff i (w ω) (c ω) (t,x))
      have hsum := Finset.measurable_sum Finset.univ (fun i _ => hterm i)
      convert hsum using 1
      funext ω
      rw [(Q ω).optimalScalarValue_eq_bellmanValue (mixedEmpiricalInstance_integrable P hP known (y ω)) (hw0 ω) (hc0 ω)]
      unfold Instance.bellmanValue
      exact Finset.sum_congr rfl fun i _ => integral_prod _
        ((Q ω).integrable_bellmanFirstPayoff (mixedEmpiricalInstance_integrable P hP known (y ω)) i (hw0 ω).le (hc0 ω))

end ProphetSecretary.Model
