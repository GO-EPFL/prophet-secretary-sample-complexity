import ProphetSecretary.Analysis.MultilevelEstimatorMoments
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fixed points of finite-rank recursions

Iteration from zero stabilizes after the rank of the current state plus one.
The error between a comparison function and this stabilized value is bounded
by its one-step residual and the payoff coefficient.
-/

open MeasureTheory Filter

namespace ProphetSecretary.Analysis

variable {State Seed Transition : Type*}
  [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]

/-- One expected update, with the prescribed terminal value. -/
noncomputable def finiteRankStep (D : MultilevelRecursion State Seed Transition ℝ)
    (μ : Measure Seed) (v : State → ℝ) (x : State) : ℝ :=
  if D.isEmpty x then D.emptyValue x else D.offset x + D.coefficient x *
    ∫ seed, D.payoff x (D.sample x seed) (v (D.child x (D.sample x seed))) ∂μ

lemma measurable_finiteRankIntegrand (D : MultilevelRecursion State Seed Transition ℝ)
    (hD : D.IsMeasurable) {v : State → ℝ} (hv : Measurable v) :
    Measurable (fun q : State × Seed =>
      D.payoff q.1 (D.sample q.1 q.2) (v (D.child q.1 (D.sample q.1 q.2)))) :=
  hD.payoff.comp ((measurable_fst.prodMk hD.sample).prodMk
    (hv.comp (hD.child.comp (measurable_fst.prodMk hD.sample))))

lemma measurable_finiteRankStep (D : MultilevelRecursion State Seed Transition ℝ)
    (hD : D.IsMeasurable) (μ : Measure Seed) [IsProbabilityMeasure μ]
    {v : State → ℝ} (hv : Measurable v) : Measurable (finiteRankStep D μ v) := by
  unfold finiteRankStep
  exact hD.emptyValue.ite (hD.isEmpty (measurableSet_singleton true))
    (hD.offset.add (hD.coefficient.mul
      ((measurable_finiteRankIntegrand D hD hv).stronglyMeasurable.integral_prod_right'
        (ν := μ)).measurable))

lemma integrable_finiteRankIntegrand (D : MultilevelRecursion State Seed Transition ℝ)
    (hD : D.IsMeasurable) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (hPay : ∀ x o w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x o w ∧ D.payoff x o w ≤ 1)
    {v : State → ℝ} (hv : Measurable v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 5) (x : State) :
    Integrable (fun seed => D.payoff x (D.sample x seed) (v (D.child x (D.sample x seed)))) μ := by
  apply Integrable.of_bound ((measurable_finiteRankIntegrand D hD hv).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  exact ae_of_all _ (fun seed => by
    let c := D.child x (D.sample x seed)
    have h := hPay x (D.sample x seed) (v c) (hvb c).1 (hvb c).2
    change ‖D.payoff x (D.sample x seed) (v c)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2)

lemma finiteRankStep_bounds (D : MultilevelRecursion State Seed Transition ℝ)
    (hD : D.IsMeasurable) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hOffset : ∀ x, 0 ≤ D.offset x ∧ D.offset x ≤ 4)
    (hCoeff : ∀ x, 0 ≤ D.coefficient x ∧ D.coefficient x ≤ 1/4)
    (hPay : ∀ x o w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x o w ∧ D.payoff x o w ≤ 1)
    {v : State → ℝ} (hv : Measurable v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 5) (x : State) :
    0 ≤ finiteRankStep D μ v x ∧ finiteRankStep D μ v x ≤ 5 := by
  let f := fun seed => D.payoff x (D.sample x seed) (v (D.child x (D.sample x seed)))
  have hf (s : Seed) : 0 ≤ f s ∧ f s ≤ 1 := hPay _ _ _ (hvb _).1 (hvb _).2
  have h0 : 0 ≤ ∫ s, f s ∂μ := integral_nonneg (fun s => (hf s).1)
  have h1 : (∫ s, f s ∂μ) ≤ 1 := calc
    _ ≤ ∫ _s : Seed, (1 : ℝ) ∂μ := integral_mono
      (integrable_finiteRankIntegrand D hD μ hPay hv hvb x) (integrable_const _) (fun s => (hf s).2)
    _ = 1 := by simp
  cases he : D.isEmpty x
  · have hP : D.coefficient x * (∫ s, f s ∂μ) ≤ 1/4 := calc
      _ ≤ D.coefficient x * 1 := mul_le_mul_of_nonneg_left h1 (hCoeff x).1
      _ ≤ _ := by simpa using (hCoeff x).2
    simp only [finiteRankStep, he, Bool.false_eq_true, if_false]
    change 0 ≤ D.offset x + D.coefficient x * (∫ s, f s ∂μ) ∧
      D.offset x + D.coefficient x * (∫ s, f s ∂μ) ≤ 5
    exact ⟨add_nonneg (hOffset x).1 (mul_nonneg (hCoeff x).1 h0), by linarith [(hOffset x).2]⟩
  · simpa only [finiteRankStep, he, if_true] using hEmpty x he

/-- Iteration from zero with one step per level of the state rank. -/
noncomputable def finiteRankValue (D : MultilevelRecursion State Seed Transition ℝ)
    (μ : Measure Seed) : ℕ → State → ℝ
  | 0 => fun _ => 0
  | m + 1 => finiteRankStep D μ (finiteRankValue D μ m)

lemma measurable_finiteRankValue (D : MultilevelRecursion State Seed Transition ℝ)
    (hD : D.IsMeasurable) (μ : Measure Seed) [IsProbabilityMeasure μ] (m : ℕ) :
    Measurable (finiteRankValue D μ m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih => exact measurable_finiteRankStep D hD μ ih

lemma finiteRankValue_bounds (D : MultilevelRecursion State Seed Transition ℝ)
    (hD : D.IsMeasurable) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hOffset : ∀ x, 0 ≤ D.offset x ∧ D.offset x ≤ 4)
    (hCoeff : ∀ x, 0 ≤ D.coefficient x ∧ D.coefficient x ≤ 1/4)
    (hPay : ∀ x o w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x o w ∧ D.payoff x o w ≤ 1)
    (m : ℕ) : ∀ x, 0 ≤ finiteRankValue D μ m x ∧ finiteRankValue D μ m x ≤ 5 := by
  induction m with
  | zero => intro x; change 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 5; norm_num
  | succ m ih =>
    exact finiteRankStep_bounds D hD μ hEmpty hOffset hCoeff hPay
      (measurable_finiteRankValue D hD μ m) ih

omit [MeasurableSpace State] [MeasurableSpace Transition] in
lemma finiteRankValue_stabilizes (D : MultilevelRecursion State Seed Transition ℝ)
    (μ : Measure Seed) (rank : State → ℕ)
    (hRank : ∀ x, D.isEmpty x = false → ∀ s, rank (D.child x (D.sample x s)) < rank x)
    (m : ℕ) (x : State) (hx : rank x < m) :
    finiteRankValue D μ (m+1) x = finiteRankValue D μ m x := by
  induction m generalizing x with
  | zero => omega
  | succ m ih =>
    change finiteRankStep D μ (finiteRankValue D μ (m+1)) x =
      finiteRankStep D μ (finiteRankValue D μ m) x
    cases he : D.isEmpty x
    · simp only [finiteRankStep, he, Bool.false_eq_true, if_false]
      congr 1
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun s => by
        dsimp
        rw [ih _ (lt_of_lt_of_le (hRank x he s) (by omega))])
    · simp only [finiteRankStep, he, if_true]

omit [MeasurableSpace State] [MeasurableSpace Transition] in
lemma finiteRankValue_fixed (D : MultilevelRecursion State Seed Transition ℝ)
    (μ : Measure Seed) (rank : State → ℕ)
    (hRank : ∀ x, D.isEmpty x = false → ∀ s, rank (D.child x (D.sample x s)) < rank x)
    (M : ℕ) (x : State) (hx : rank x ≤ M) :
    finiteRankValue D μ (M+1) x = finiteRankStep D μ (finiteRankValue D μ (M+1)) x :=
  (finiteRankValue_stabilizes D μ rank hRank (M+1) x (by omega)).symm

/-- The one-step residual controls the error against a fixed point by
induction on the current state's rank. -/
theorem finiteRank_distance_le (D : MultilevelRecursion State Seed Transition ℝ)
    (hD : D.IsMeasurable) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (rank : State → ℕ)
    (hRank : ∀ x, D.isEmpty x = false → ∀ s, rank (D.child x (D.sample x s)) < rank x)
    (hCoeff : ∀ x, 0 ≤ D.coefficient x ∧ D.coefficient x ≤ 1/4)
    (hPay : ∀ x o w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x o w ∧ D.payoff x o w ≤ 1)
    (hLip : ∀ x o, LipschitzWith 1 (D.payoff x o))
    (v w : State → ℝ) (hv : Measurable v) (hw : Measurable w)
    (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 5) (hwb : ∀ x, 0 ≤ w x ∧ w x ≤ 5)
    (hwf : ∀ x, w x = finiteRankStep D μ w x)
    (E : ℝ) (hE : 0 ≤ E) (hres : ∀ x, |v x - finiteRankStep D μ v x| ≤ E) (x : State) :
    |v x - w x| ≤ 4*E/3 := by
  induction x using (measure rank).wf.induction with
  | h x ih =>
    have hR := hres x
    cases hx : D.isEmpty x
    · let f := fun s => D.payoff x (D.sample x s) (v (D.child x (D.sample x s)))
      let g := fun s => D.payoff x (D.sample x s) (w (D.child x (D.sample x s)))
      have hf : Integrable f μ := integrable_finiteRankIntegrand D hD μ hPay hv hvb x
      have hg : Integrable g μ := integrable_finiteRankIntegrand D hD μ hPay hw hwb x
      have hp (s : Seed) : |f s - g s| ≤ 4*E/3 := by
        have h := (hLip x (D.sample x s)).dist_le_mul
          (v (D.child x (D.sample x s))) (w (D.child x (D.sample x s)))
        exact (by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h :
          |f s-g s| ≤ |v (D.child x (D.sample x s))-w (D.child x (D.sample x s))|).trans
          (ih _ (hRank x hx s))
      have hi : |(∫ s, f s ∂μ) - (∫ s, g s ∂μ)| ≤ 4*E/3 := calc
        _ = |∫ s, f s - g s ∂μ| := by rw [integral_sub hf hg]
        _ ≤ ∫ s, |f s-g s| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ _s : Seed, (4*E/3) ∂μ := integral_mono (hf.sub hg).abs (integrable_const _) hp
        _ = _ := by simp
      have hstep : |finiteRankStep D μ v x - w x| ≤ E/3 := by
        rw [hwf x]
        simp only [finiteRankStep, hx, Bool.false_eq_true, if_false]
        change |(D.offset x + D.coefficient x * (∫ s, f s ∂μ)) -
          (D.offset x + D.coefficient x * (∫ s, g s ∂μ))| ≤ _
        rw [show (D.offset x + D.coefficient x * (∫ s, f s ∂μ)) -
          (D.offset x + D.coefficient x * (∫ s, g s ∂μ)) =
          D.coefficient x * ((∫ s, f s ∂μ) - (∫ s, g s ∂μ)) by ring,
          abs_mul, abs_of_nonneg (hCoeff x).1]
        calc
          _ ≤ D.coefficient x * (4*E/3) := mul_le_mul_of_nonneg_left hi (hCoeff x).1
          _ ≤ (1/4 : ℝ) * (4*E/3) := mul_le_mul_of_nonneg_right (hCoeff x).2 (by positivity)
          _ = _ := by ring
      calc
        _ = |(v x - finiteRankStep D μ v x) + (finiteRankStep D μ v x - w x)| := by ring_nf
        _ ≤ |v x - finiteRankStep D μ v x| + |finiteRankStep D μ v x - w x| := abs_add_le _ _
        _ ≤ E + E/3 := add_le_add hR hstep
        _ = _ := by ring
    · have heq : finiteRankStep D μ v x = w x := by
        rw [hwf x]; simp only [finiteRankStep, hx, if_true]
      rw [← heq]
      exact hR.trans (by linarith)

end ProphetSecretary.Analysis
