import ProphetSecretary.Model.ScalarCoefficientMeasurability
import ProphetSecretary.Model.EmpiricalPolicy
import ProphetSecretary.Model.BellmanPerformance

/-!
# Joint continuation measurability with observed coefficients

The scalar coefficients may depend measurably on training data and an
independent seed. The actual unseen identity set still comes from the observed
history, including zero-valued arrivals. Joint measurability alone does not
permit a coefficient to vary during an arrival-time integral.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma Instance.measurable_valueThreshold_coefficients (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c t : Ω → ℝ}
    {A : Ω → Finset (Fin n)} {i : Ω → Fin n}
    (hw : Measurable w) (hc : Measurable c) (ht : Measurable t) (hA : Measurable A) (hi : Measurable i)
    (hw0 : ∀ ω, 0<w ω) (hc0 : ∀ ω, 0≤c ω) :
    Measurable (fun ω => P.valueThreshold (w ω) (c ω) (A ω) (t ω) (i ω)) := by
  have hfixed (B : Finset (Fin n)) (j : Fin n) :
      Measurable (fun ω => P.valueThreshold (w ω) (c ω) B (t ω) j) := by
    have hv := (P.restrictTo (B.erase j)).measurable_scalarValue_coefficients
      (P.restrictTo_integrable_maximum (B.erase j) hP) hw
      (hc.mul (measurable_const.max (measurable_const.sub ht)))
      (fun ω => (hw0 ω).le) (fun ω => mul_nonneg (hc0 ω) (le_max_left 0 (1-t ω)))
    convert hv.div hw using 1
    funext ω
    rfl
  have hall : Measurable (fun z : (Finset (Fin n) × Fin n) × Ω =>
      P.valueThreshold (w z.2) (c z.2) z.1.1 (t z.2) z.1.2) :=
    measurable_from_prod_countable_right (fun p => hfixed p.1 p.2)
  have hpair : Measurable (fun ω => ((A ω,i ω),ω)) := (hA.prodMk hi).prodMk measurable_id
  convert hall.comp hpair using 1
  funext ω
  rfl

lemma Instance.measurable_continuationAtArrival_coefficients (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : Ω → ℝ} {x u : Ω → Fin n → ℝ}
    (hw : Measurable w) (hc : Measurable c) (hw0 : ∀ ω, 0<w ω) (hc0 : ∀ ω, 0≤c ω)
    (hx : ∀ j, Measurable (fun ω => x ω j)) (hu : ∀ j, Measurable (fun ω => u ω j)) (i : Fin n) :
    Measurable (fun ω => P.continuationAtArrival (w ω) (c ω) (x ω) (u ω) i) := by
  have hH := measurable_history Finset.univ hx hu (hu i)
  have hUnseen := measurable_unseen.comp hH
  have hθ := P.measurable_valueThreshold_coefficients hP (i:=fun _ => i) hw hc (hu i) hUnseen measurable_const hw0 hc0
  have hm := hw.mul hθ
  convert hm using 1
  funext ω
  exact P.continuationAtArrival_eq_threshold (hw0 ω) (c ω) (x ω) (u ω) i

lemma measurable_totalEmpirical_continuationAtArrival_coefficients {k : ℕ} [NeZero k]
    {y : Ω → Reservoir n k} {w c : Ω → ℝ} {x u : Ω → Fin n → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hw : Measurable w) (hc : Measurable c)
    (hw0 : ∀ ω, 0<w ω) (hc0 : ∀ ω, 0≤c ω)
    (hx : ∀ j, Measurable (fun ω => x ω j)) (hu : ∀ j, Measurable (fun ω => u ω j)) (i : Fin n) :
    Measurable (fun ω => (totalEmpiricalInstance (y ω)).continuationAtArrival (w ω) (c ω) (x ω) (u ω) i) := by
  have hH := measurable_history Finset.univ hx hu (hu i)
  have hUnseen := measurable_unseen.comp hH
  have hθ := measurable_totalEmpirical_valueThreshold (i:=fun _ => i) hy hw hc (hu i) hUnseen measurable_const hw0 hc0
  have hm := hw.mul hθ
  convert hm using 1
  funext ω
  exact (totalEmpiricalInstance (y ω)).continuationAtArrival_eq_threshold (hw0 ω) (c ω) (x ω) (u ω) i

lemma Policy.measurable_arrivalBellmanLoss_coefficients {Seed : Type*} [MeasurableSpace Seed]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : Ω → ℝ} {r : Ω → Seed} {x u : Ω → Fin n → ℝ}
    (hw : Measurable w) (hc : Measurable c) (hw0 : ∀ ω, 0<w ω) (hc0 : ∀ ω, 0≤c ω)
    (hr : Measurable r) (hx : ∀ j, Measurable (fun ω => x ω j)) (hu : ∀ j, Measurable (fun ω => u ω j)) (i : Fin n) :
    Measurable (fun ω => π.arrivalBellmanLoss P (w ω) (c ω) (r ω) (x ω) (u ω) i) := by
  have hX := hw.mul (hx i)
  have hV := P.measurable_continuationAtArrival_coefficients hP hw hc hw0 hc0 hx hu i
  have hAct : MeasurableSet {ω | π.action (r ω) Finset.univ (x ω) (u ω) i=true} :=
    measurableSet_eq_fun (π.measurable_action hπ hr hx hu Finset.univ i) measurable_const
  exact (hX.max hV).sub (Measurable.ite hAct hX hV)

end ProphetSecretary.Model
