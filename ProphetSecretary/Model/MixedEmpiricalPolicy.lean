import ProphetSecretary.Model.MixedEmpiricalThresholdMeasurability
import ProphetSecretary.Model.EmpiricalPolicy

/-!
# Canonical rules using exact known and empirical unknown laws

The actual rule reads known marginal laws, stored samples, current offer and
observed history. Its unrestricted optimality is inherited from the proved
finite Bellman theorem. Invalid scalar coefficients have the same totalization
on every raw sample outcome.
-/

open MeasureTheory
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]

noncomputable def mixedEmpiricalValueThreshold (P : Instance n) (known : Finset (Fin n)) (y : Reservoir n k) (w c : ℝ)
    (A : Finset (Fin n)) (t : ℝ) (i : Fin n) : ℝ :=
  (mixedEmpiricalInstance P known y).valueThreshold (positiveRewardWeight w) (max 0 c) A t i

lemma mixedEmpiricalValueThreshold_eq (P : Instance n) (known : Finset (Fin n)) (y : Reservoir n k) {w c : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (A : Finset (Fin n)) (t : ℝ) (i : Fin n) :
    mixedEmpiricalValueThreshold P known y w c A t i = (mixedEmpiricalInstance P known y).valueThreshold w c A t i := by
  simp only [mixedEmpiricalValueThreshold, positiveRewardWeight_eq hw, max_eq_right hc]

lemma measurable_mixedEmpiricalValueThreshold (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {w c t : Ω → ℝ}
    {A : Ω → Finset (Fin n)} {i : Ω → Fin n}
    (hy : ∀ q j, Measurable fun ω => y ω q j) (hw : Measurable w) (hc : Measurable c)
    (ht : Measurable t) (hA : Measurable A) (hi : Measurable i) :
    Measurable fun ω => mixedEmpiricalValueThreshold P known (y ω) (w ω) (c ω) (A ω) (t ω) (i ω) :=
  measurable_mixedEmpirical_valueThreshold P hP known hy (measurable_positiveRewardWeight.comp hw)
    (measurable_const.max hc) ht hA hi (fun ω => positiveRewardWeight_pos (w ω)) (fun _ => le_max_left _ _)

/-- A single measurable rule jointly parameterized by every real sample array and
both scalar weights. The policy observes its training output, then ordinary online history. -/
noncomputable def mixedEmpiricalCanonicalPolicy (P : Instance n) (known : Finset (Fin n)) : Policy (Reservoir n k × (ℝ × ℝ)) n where
  decide p t i x h := decide (mixedEmpiricalValueThreshold P known p.1 p.2.1 p.2.2 (unseen h) t i ≤ x)

lemma mixedEmpiricalCanonicalPolicy_isMeasurable (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) :
    (mixedEmpiricalCanonicalPolicy (n := n) (k := k) P known).IsMeasurable := by
  classical
  let T := (Reservoir n k × (ℝ × ℝ)) × (ℝ × (Fin n × (ℝ × History n)))
  have hy (q : Fin n) (j : Fin k) : Measurable (fun z : T => z.1.1 q j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply q).comp (measurable_fst.comp measurable_fst))
  have hw : Measurable (fun z : T => z.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hc : Measurable (fun z : T => z.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have ht : Measurable (fun z : T => z.2.1) := measurable_fst.comp measurable_snd
  have hi : Measurable (fun z : T => z.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hx : Measurable (fun z : T => z.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hH : Measurable (fun z : T => z.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hθ := measurable_mixedEmpiricalValueThreshold P hP known hy hw hc ht (measurable_unseen.comp hH) hi
  have hs := measurableSet_le hθ hx
  change Measurable (fun z : T => decide (mixedEmpiricalValueThreshold P known z.1.1 z.1.2.1 z.1.2.2 (unseen z.2.2.2.2) z.2.1 z.2.2.1 ≤ z.2.2.2.1))
  have hIf : Measurable (fun z : T => if mixedEmpiricalValueThreshold P known z.1.1 z.1.2.1 z.1.2.2 (unseen z.2.2.2.2) z.2.1 z.2.2.1 ≤ z.2.2.2.1 then true else false) :=
    Measurable.ite hs measurable_const measurable_const
  convert hIf using 1
  funext z
  split_ifs <;> simp_all

/-- Fixing valid coefficients and an array gives precisely the already-proved
canonical empirical policy, rather than an abstract measurable optimizer selection. -/
lemma mixedEmpiricalCanonicalPolicy_decide (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (y : Reservoir n k) {w c : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (t : ℝ) (i : Fin n) (x : ℝ) (h : History n) :
    (mixedEmpiricalCanonicalPolicy (n := n) (k := k) P known).decide (y, (w, c)) t i x h =
      ((mixedEmpiricalInstance P known y).valuePolicy (mixedEmpiricalInstance_integrable P hP known y) hw.le hc).rule.decide
        () t i x h := by
  change decide (mixedEmpiricalValueThreshold P known y w c (unseen h) t i ≤ x) = _
  rw [mixedEmpiricalValueThreshold_eq P known y hw hc]
  rfl

/-- Unknown true laws are not information used by this actual policy. -/
lemma mixedEmpiricalCanonicalPolicy_congr_known {P Q : Instance n} (known : Finset (Fin n))
    (hknown : ∀ i∈known, P.law i=Q.law i) :
    mixedEmpiricalCanonicalPolicy (k:=k) P known = mixedEmpiricalCanonicalPolicy Q known := by
  apply congrArg Policy.mk
  funext p t i x h
  simp only [mixedEmpiricalValueThreshold,mixedEmpiricalInstance_congr_known known hknown]
  rfl

end ProphetSecretary.Model
