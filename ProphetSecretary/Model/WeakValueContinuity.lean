import ProphetSecretary.Probability.WeakStopLoss
import ProphetSecretary.Model.StopLossStability

/-!
# Weak-law continuity of the actual finite scalar optimum

Uniform stop-loss convergence for each of finitely many capped marginals is
inserted into the proved general-policy Bellman stability estimate. The
optimization still ranges over all admissible randomized history-dependent
policies; no convergence of their optimizers is assumed or concluded.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def Instance.marginalProbabilityLaw (P : Instance n) (i : Fin n) : ProbabilityMeasure ℝ :=
  ⟨P.law i,P.probability i⟩

/-- A symmetric explicit error bound, with no additional factor beyond the
sum of the individual stop-loss errors. -/
theorem Instance.optimalScalarValue_abs_sub_le_of_stopLoss_error (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (herror : ∀ i q, |stopLoss (P.law i) q-stopLoss (Q.law i) q| ≤ d i)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    |optimalScalarValue P w c-optimalScalarValue Q w c| ≤ w * ∑ i, d i := by
  by_cases hw0 : w = 0
  · subst w
    rw [optimalScalarValue_zero_rewardWeight P hc,optimalScalarValue_zero_rewardWeight Q hc]
    simp
  · have hwPos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    have hPQ := P.optimalScalarValue_le_of_stopLoss_error Q hP hQ d hd
      (fun i q => by have h := (abs_le.mp (herror i q)).2; linarith) hwPos hc
    have hQP := Q.optimalScalarValue_le_of_stopLoss_error P hQ hP d hd
      (fun i q => by have h := (abs_le.mp (herror i q)).1; linarith) hwPos hc
    exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Law continuity is uniform for bounded reward weight and every nonnegative
duration weight, since the stability error is independent of c. -/
theorem optimalScalarValue_uniform_weak_law_error {Γ : Type*} {l : Filter Γ}
    (Ps : Γ → Instance n) (P : Instance n) (H W : ℝ≥0)
    (hsCap : ∀ m i, ∀ᵐ x ∂(Ps m).law i, x ≤ (H : ℝ))
    (hCap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hweak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) l
      (𝓝 (P.marginalProbabilityLaw i))) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in l, ∀ w c : ℝ, 0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c →
      |optimalScalarValue (Ps m) w c-optimalScalarValue P w c| < ε := by
  have hUniform (i : Fin n) :
      TendstoUniformly (fun m q => stopLoss ((Ps m).law i) q) (stopLoss (P.law i)) l := by
    apply stopLoss_tendstoUniformly_of_bounded (hweak i) H
    · intro m
      filter_upwards [(Ps m).nonnegative i,hsCap m i] with x hx0 hxH
      exact ⟨hx0,hxH⟩
    · filter_upwards [P.nonnegative i,hCap i] with x hx0 hxH
      exact ⟨hx0,hxH⟩
  intro ε hε
  let d : ℝ := ε / (((W : ℝ)+1)*((n : ℝ)+1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hEach (i : Fin n) : ∀ᶠ m in l, ∀ q, |stopLoss ((Ps m).law i) q-stopLoss (P.law i) q| ≤ d := by
    filter_upwards [(Metric.tendstoUniformly_iff.mp (hUniform i)) d hd] with m hm
    intro q
    simpa only [Real.dist_eq,abs_sub_comm] using (hm q).le
  filter_upwards [eventually_all.mpr hEach] with m hm
  intro w c hw hW hc
  have hBound := (Ps m).optimalScalarValue_abs_sub_le_of_stopLoss_error P
    ((Ps m).integrable_maximum_of_bounded (hsCap m)) (P.integrable_maximum_of_bounded hCap)
    (fun _ => d) (fun _ => hd.le) hm hw hc
  have hBudget : ((W : ℝ)+1) * ∑ _i : Fin n, d = ε*(n : ℝ)/((n : ℝ)+1) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp [d]
    field_simp
  have hcompare : w * ∑ _i : Fin n, d ≤ ((W : ℝ)+1) * ∑ _i : Fin n, d :=
    mul_le_mul_of_nonneg_right (hW.trans (by linarith)) (Finset.sum_nonneg fun _ _ => hd.le)
  apply (hBound.trans hcompare).trans_lt
  rw [hBudget]
  exact (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)+1)).mpr (by nlinarith)

/-- Fixed-size cap-bounded independent instances have weakly continuous scalar
optimum. Both weights may be zero; the empty instance is included. -/
theorem optimalScalarValue_tendsto_of_coordinatewise_weak {Γ : Type*} {l : Filter Γ}
    (Ps : Γ → Instance n) (P : Instance n) (H : ℝ≥0)
    (hsCap : ∀ m i, ∀ᵐ x ∂(Ps m).law i, x ≤ (H : ℝ))
    (hCap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hweak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) l
      (𝓝 (P.marginalProbabilityLaw i)))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Tendsto (fun m => optimalScalarValue (Ps m) w c) l (𝓝 (optimalScalarValue P w c)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [optimalScalarValue_uniform_weak_law_error Ps P H ⟨w,hw⟩ hsCap hCap hweak ε hε] with m hm
  simpa only [Real.dist_eq] using hm w c hw le_rfl hc

end ProphetSecretary.Model
