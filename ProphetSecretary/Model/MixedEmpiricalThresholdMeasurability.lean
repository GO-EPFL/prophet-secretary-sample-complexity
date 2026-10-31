import ProphetSecretary.Model.MixedEmpiricalValueMeasurability
import ProphetSecretary.Model.EmpiricalPolicy

/-!
# Joint thresholds with known and empirical marginals

Every unseen identity is retained. Known marginals contribute their exact laws,
and unknown ones their stored samples. The scalar coefficients and observed
history may vary jointly and measurably; this does not permit a scalar to change
while time is integrated in the later statistical argument.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_mixedEmpirical_valueThreshold (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {w c t : Ω → ℝ}
    {A : Ω → Finset (Fin n)} {i : Ω → Fin n}
    (hy : ∀ q l, Measurable fun ω => y ω q l) (hw : Measurable w) (hc : Measurable c)
    (ht : Measurable t) (hA : Measurable A) (hi : Measurable i)
    (hw0 : ∀ ω, 0<w ω) (hc0 : ∀ ω, 0≤c ω) :
    Measurable fun ω => (mixedEmpiricalInstance P known (y ω)).valueThreshold
      (w ω) (c ω) (A ω) (t ω) (i ω) := by
  have hfixed (B : Finset (Fin n)) (j : Fin n) : Measurable (fun ω =>
      (mixedEmpiricalInstance P known (y ω)).valueThreshold (w ω) (c ω) B (t ω) j) := by
    have hv := measurable_optimalScalarValue_mixedEmpirical (P.restrictTo (B.erase j))
      (P.restrictTo_integrable_maximum _ hP) (knownInState known (B.erase j))
      (y:=fun ω q l => y ω (stateEmbedding (B.erase j) q) l)
      (w:=w) (c:=fun ω => c ω*max 0 (1-t ω))
      (fun q l => hy _ l) hw (hc.mul (measurable_const.max (measurable_const.sub ht)))
      hw0 (fun ω => mul_nonneg (hc0 ω) (le_max_left _ _))
    convert hv.div hw using 1
    funext ω
    rw [Instance.valueThreshold,Instance.continuationValue,mixedEmpiricalInstance_restrictTo]
    rfl
  have hall : Measurable (fun z : (Finset (Fin n) × Fin n) × Ω =>
      (mixedEmpiricalInstance P known (y z.2)).valueThreshold (w z.2) (c z.2) z.1.1 (t z.2) z.1.2) :=
    measurable_from_prod_countable_right (fun p => hfixed p.1 p.2)
  convert hall.comp ((hA.prodMk hi).prodMk measurable_id) using 1
  funext ω
  rfl

lemma measurable_mixedEmpirical_continuationAtArrival (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {w c : Ω → ℝ} {x u : Ω → Fin n → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hw : Measurable w) (hc : Measurable c)
    (hw0 : ∀ ω, 0<w ω) (hc0 : ∀ ω, 0≤c ω)
    (hx : ∀ j, Measurable (fun ω => x ω j)) (hu : ∀ j, Measurable (fun ω => u ω j)) (i : Fin n) :
    Measurable (fun ω => (mixedEmpiricalInstance P known (y ω)).continuationAtArrival
      (w ω) (c ω) (x ω) (u ω) i) := by
  have hH := measurable_history Finset.univ hx hu (hu i)
  have hUnseen := measurable_unseen.comp hH
  have hθ := measurable_mixedEmpirical_valueThreshold P hP known (i:=fun _ => i)
    hy hw hc (hu i) hUnseen measurable_const hw0 hc0
  have hm := hw.mul hθ
  convert hm using 1
  funext ω
  exact (mixedEmpiricalInstance P known (y ω)).continuationAtArrival_eq_threshold
    (hw0 ω) (c ω) (x ω) (u ω) i

end ProphetSecretary.Model
