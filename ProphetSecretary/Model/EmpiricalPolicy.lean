import ProphetSecretary.Model.EmpiricalValueMeasurability

/-!
# Empirical canonical policies with selected weights

The empirical array and both scalar coefficients may vary measurably together.
Invalid coefficients are totalized outside the paper's parameter range. On positive
reward and nonnegative duration weights the rule is exactly the canonical empirical
optimizer, including on null training outcomes after nonnegative array totalization.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]

/-- Joint thresholds retain the complete unseen-identity set, including observed zeros. -/
lemma measurable_totalEmpirical_valueThreshold
    {y : Ω → Reservoir n k} {w c t : Ω → ℝ}
    {A : Ω → Finset (Fin n)} {i : Ω → Fin n}
    (hy : ∀ q j, Measurable fun ω => y ω q j) (hw : Measurable w) (hc : Measurable c)
    (ht : Measurable t) (hA : Measurable A) (hi : Measurable i)
    (hw0 : ∀ ω, 0 < w ω) (hc0 : ∀ ω, 0 ≤ c ω) :
    Measurable fun ω => (totalEmpiricalInstance (y ω)).valueThreshold
      (w ω) (c ω) (A ω) (t ω) (i ω) := by
  have hfixed (B : Finset (Fin n)) (q : Fin n) :
      Measurable fun ω => (totalEmpiricalInstance (y ω)).valueThreshold (w ω) (c ω) B (t ω) q := by
    have hv := measurable_optimalScalarValue_totalEmpirical
      (y := fun ω j l => y ω (stateEmbedding (B.erase q) j) l)
      (w := w) (c := fun ω => c ω * max 0 (1 - t ω))
      (fun j l => hy _ l) hw (hc.mul (measurable_const.max (measurable_const.sub ht)))
      hw0 (fun ω => mul_nonneg (hc0 ω) (le_max_left _ _))
    convert hv.div hw using 1
    funext ω
    rw [Instance.valueThreshold, Instance.continuationValue, totalEmpiricalInstance_restrictTo]
    rfl
  have hall : Measurable (fun z : (Finset (Fin n) × Fin n) × Ω =>
      (totalEmpiricalInstance (y z.2)).valueThreshold (w z.2) (c z.2) z.1.1 (t z.2) z.1.2) :=
    measurable_from_prod_countable_right (fun p => hfixed p.1 p.2)
  convert hall.comp ((hA.prodMk hi).prodMk measurable_id) using 1
  funext ω
  rfl

/-- A positive totalization, equal to the reward coefficient on its valid domain. -/
noncomputable def positiveRewardWeight (w : ℝ) : ℝ := if 0 < w then w else 1

lemma positiveRewardWeight_pos (w : ℝ) : 0 < positiveRewardWeight w := by
  unfold positiveRewardWeight
  split_ifs with h
  · exact h
  · norm_num

lemma positiveRewardWeight_eq {w : ℝ} (hw : 0 < w) : positiveRewardWeight w = w := by
  simp [positiveRewardWeight, hw]

lemma measurable_positiveRewardWeight : Measurable positiveRewardWeight :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_id measurable_const

noncomputable def empiricalValueThreshold (y : Reservoir n k) (w c : ℝ)
    (A : Finset (Fin n)) (t : ℝ) (i : Fin n) : ℝ :=
  (totalEmpiricalInstance y).valueThreshold (positiveRewardWeight w) (max 0 c) A t i

lemma empiricalValueThreshold_eq (y : Reservoir n k) {w c : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (A : Finset (Fin n)) (t : ℝ) (i : Fin n) :
    empiricalValueThreshold y w c A t i = (totalEmpiricalInstance y).valueThreshold w c A t i := by
  simp only [empiricalValueThreshold, positiveRewardWeight_eq hw, max_eq_right hc]

lemma measurable_empiricalValueThreshold
    {y : Ω → Reservoir n k} {w c t : Ω → ℝ}
    {A : Ω → Finset (Fin n)} {i : Ω → Fin n}
    (hy : ∀ q j, Measurable fun ω => y ω q j) (hw : Measurable w) (hc : Measurable c)
    (ht : Measurable t) (hA : Measurable A) (hi : Measurable i) :
    Measurable fun ω => empiricalValueThreshold (y ω) (w ω) (c ω) (A ω) (t ω) (i ω) :=
  measurable_totalEmpirical_valueThreshold hy (measurable_positiveRewardWeight.comp hw)
    (measurable_const.max hc) ht hA hi (fun ω => positiveRewardWeight_pos (w ω)) (fun _ => le_max_left _ _)

/-- A single measurable rule jointly parameterized by every real sample array and
both scalar weights. The policy observes its training output, then ordinary online history. -/
noncomputable def empiricalCanonicalPolicy : Policy (Reservoir n k × (ℝ × ℝ)) n where
  decide p t i x h := decide (empiricalValueThreshold p.1 p.2.1 p.2.2 (unseen h) t i ≤ x)

lemma empiricalCanonicalPolicy_isMeasurable :
    (empiricalCanonicalPolicy (n := n) (k := k)).IsMeasurable := by
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
  have hθ := measurable_empiricalValueThreshold hy hw hc ht (measurable_unseen.comp hH) hi
  have hs := measurableSet_le hθ hx
  change Measurable (fun z : T => decide (empiricalValueThreshold z.1.1 z.1.2.1 z.1.2.2 (unseen z.2.2.2.2) z.2.1 z.2.2.1 ≤ z.2.2.2.1))
  have hIf : Measurable (fun z : T => if empiricalValueThreshold z.1.1 z.1.2.1 z.1.2.2 (unseen z.2.2.2.2) z.2.1 z.2.2.1 ≤ z.2.2.2.1 then true else false) :=
    Measurable.ite hs measurable_const measurable_const
  convert hIf using 1
  funext z
  split_ifs <;> simp_all

/-- Fixing valid coefficients and an array gives precisely the already-proved
canonical empirical policy, rather than an abstract measurable optimizer selection. -/
lemma empiricalCanonicalPolicy_decide (y : Reservoir n k) {w c : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (t : ℝ) (i : Fin n) (x : ℝ) (h : History n) :
    (empiricalCanonicalPolicy (n := n) (k := k)).decide (y, (w, c)) t i x h =
      ((totalEmpiricalInstance y).valuePolicy (totalEmpiricalInstance_integrable y) hw.le hc).rule.decide
        () t i x h := by
  change decide (empiricalValueThreshold y w c (unseen h) t i ≤ x) = _
  rw [empiricalValueThreshold_eq y hw hc]
  rfl

end ProphetSecretary.Model
