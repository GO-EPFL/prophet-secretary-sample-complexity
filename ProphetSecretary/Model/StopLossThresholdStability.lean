import ProphetSecretary.Model.WeakValueContinuity
import ProphetSecretary.Model.Continuation

/-!
# Canonical threshold stability from marginal stop-loss errors

The general-policy scalar stability estimate is applied to the actual child
instance and divided by the positive reward weight. This proves threshold
stability directly, uniformly in elapsed time and duration weight, rather
than inferring optimizer behavior from value convergence alone.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma Instance.valueThreshold_abs_sub_le_of_stopLoss_error (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (herror : ∀ i q, |stopLoss (P.law i) q-stopLoss (Q.law i) q| ≤ d i)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (A : Finset (Fin n)) (t : ℝ) (i : Fin n) :
    |P.valueThreshold w c A t i-Q.valueThreshold w c A t i| ≤ ∑ j ∈ A.erase i, d j := by
  have hV := (P.restrictTo (A.erase i)).optimalScalarValue_abs_sub_le_of_stopLoss_error
    (Q.restrictTo (A.erase i)) (P.restrictTo_integrable_maximum _ hP) (Q.restrictTo_integrable_maximum _ hQ)
    (fun j => d (stateEmbedding (A.erase i) j)) (fun j => hd _)
    (fun j q => herror _ q) hw.le (mul_nonneg hc (le_max_left (0 : ℝ) (1-t)))
  rw [sum_stateEmbedding] at hV
  change |optimalScalarValue (P.restrictTo (A.erase i)) w (c*max 0 (1-t))/w-
    optimalScalarValue (Q.restrictTo (A.erase i)) w (c*max 0 (1-t))/w| ≤ _
  rw [← sub_div,abs_div,abs_of_pos hw]
  apply (div_le_iff₀ hw).mpr
  simpa only [mul_comm] using hV

/-- Uniform canonical threshold convergence under capped coordinatewise weak
laws. The statement concerns the actual threshold functions, not a chosen
representation of arbitrary competing policies. -/
theorem valueThreshold_uniform_weak_law_error {Γ : Type*} {l : Filter Γ}
    (Ps : Γ → Instance n) (P : Instance n) (H : ℝ≥0)
    (hsCap : ∀ m i, ∀ᵐ x ∂(Ps m).law i, x ≤ (H : ℝ))
    (hCap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hweak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) l (𝓝 (P.marginalProbabilityLaw i))) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in l, ∀ w c : ℝ, 0 < w → 0 ≤ c → ∀ A t i,
      |(Ps m).valueThreshold w c A t i-P.valueThreshold w c A t i| < ε := by
  have hUniform (i : Fin n) :
      TendstoUniformly (fun m q => stopLoss ((Ps m).law i) q) (stopLoss (P.law i)) l := by
    apply stopLoss_tendstoUniformly_of_bounded (hweak i) H
    · intro m
      filter_upwards [(Ps m).nonnegative i,hsCap m i] with x hx0 hxH
      exact ⟨hx0,hxH⟩
    · filter_upwards [P.nonnegative i,hCap i] with x hx0 hxH
      exact ⟨hx0,hxH⟩
  intro ε hε
  let d : ℝ := ε/((n : ℝ)+1)
  have hd : 0 < d := by dsimp [d]; positivity
  have heach (i : Fin n) : ∀ᶠ m in l, ∀ q, |stopLoss ((Ps m).law i) q-stopLoss (P.law i) q| ≤ d := by
    filter_upwards [(Metric.tendstoUniformly_iff.mp (hUniform i)) d hd] with m hm
    intro q
    simpa only [Real.dist_eq,abs_sub_comm] using (hm q).le
  filter_upwards [eventually_all.mpr heach] with m hm
  intro w c hw hc A t i
  have hθ := (Ps m).valueThreshold_abs_sub_le_of_stopLoss_error P
    ((Ps m).integrable_maximum_of_bounded (hsCap m)) (P.integrable_maximum_of_bounded hCap)
    (fun _ => d) (fun _ => hd.le) hm hw hc A t i
  have hsum : (∑ j ∈ A.erase i, d) ≤ ∑ _j : Fin n, d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => hd.le)
  apply (hθ.trans hsum).trans_lt
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  dsimp [d]
  apply (mul_div_assoc (n : ℝ) ε ((n : ℝ)+1)).symm.trans_lt
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)+1)).mpr
  nlinarith

end ProphetSecretary.Model
