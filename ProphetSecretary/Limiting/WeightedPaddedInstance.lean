import ProphetSecretary.Limiting.WeightedOrdering
import ProphetSecretary.Limiting.IndependentAppend
import ProphetSecretary.Model.TerminalZeroPadding

/-!
# Finite instances from ordered padded marginal laws

Padding by independent zero identities permits a fixed retained-prefix size
even when the original instance has fewer variables. The equality of terminal
values uses the proved causal zero-history simulation and an actual relabeling.
-/

open MeasureTheory Set BoundedContinuousFunction
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ}

noncomputable def weightOrderedPrefix (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ) : Model.Instance N where
  law i := (weightOrderedPaddedLaw P w i.val : Measure ℝ)
  probability i := (weightOrderedPaddedLaw P w i.val).prop
  nonnegative i := weightOrderedPaddedLaw_nonnegative P w i.val

noncomputable def weightOrderedRemainder (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ) : Model.Instance n where
  law i := (weightOrderedPaddedLaw P w (N+i.val) : Measure ℝ)
  probability i := (weightOrderedPaddedLaw P w (N+i.val)).prop
  nonnegative i := weightOrderedPaddedLaw_nonnegative P w (N+i.val)

lemma weightOrderedPrefix_bounded (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    ∀ i, ∀ᵐ x ∂(weightOrderedPrefix P w N).law i, x ≤ H := by
  intro i
  have hs := weightOrderedPaddedLaw_supported_interval P w hH hcap i.val
  exact (ae_iff.mpr hs).mono (fun _ hx => hx.2)

lemma weightOrderedRemainder_bounded (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    ∀ i, ∀ᵐ x ∂(weightOrderedRemainder P w N).law i, x ≤ H := by
  intro i
  have hs := weightOrderedPaddedLaw_supported_interval P w hH hcap (N+i.val)
  exact (ae_iff.mpr hs).mono (fun _ hx => hx.2)

lemma weightOrderedPrefix_append_remainder (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ) :
    (weightOrderedPrefix P w N).appendIndependent (weightOrderedRemainder P w N) =
      weightOrderedPrefix P w (N+n) := by
  apply Model.Instance.eq_of_law_eq
  funext i
  induction i using Fin.addCases <;>
    simp only [Model.Instance.appendIndependent,Fin.addCases_left,Fin.addCases_right,
      weightOrderedPrefix,weightOrderedRemainder,Fin.val_castAdd,Fin.val_natAdd]

lemma weightOrderedPrefix_full_law (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ)
    (i : Fin (n+N)) :
    ((P.restrictBy (weightedMeanPermutation P w).toEmbedding).appendZeros N).law i =
      (weightOrderedPrefix P w (N+n)).law ((finCongr (Nat.add_comm n N)) i) := by
  induction i using Fin.addCases with
  | left i =>
    simp only [Model.Instance.appendZeros,Fin.addCases_left,weightOrderedPrefix]
    change P.law (weightedMeanPermutation P w i) =
      (weightOrderedPaddedLaw P w i.val : Measure ℝ)
    rw [weightOrderedPaddedLaw_of_lt P w i.isLt]
    rfl
  | right j =>
    simp only [Model.Instance.appendZeros,Fin.addCases_right,weightOrderedPrefix]
    change Measure.dirac (0 : ℝ) = (weightOrderedPaddedLaw P w (n+j.val) : Measure ℝ)
    exact (weightOrderedPaddedLaw_of_ge P w (by omega)).symm

lemma weightOrderedPrefix_full_terminal_value (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Model.optimalTerminalScalarValue (weightOrderedPrefix P wgt (N+n)) a w c =
      Model.optimalTerminalScalarValue P a w c := by
  let R := P.restrictBy (weightedMeanPermutation P wgt).toEmbedding
  have hR := P.restrictBy_integrable_maximum (weightedMeanPermutation P wgt).toEmbedding hP
  have hS := (R.appendZeros_integrable_maximum N hR)
  have he := (R.appendZeros N).optimalTerminalScalarValue_eq_of_law_equiv
    (weightOrderedPrefix P wgt (N+n)) (finCongr (Nat.add_comm N n))
    (fun i => by
      have h := weightOrderedPrefix_full_law P wgt N ((finCongr (Nat.add_comm N n)) i)
      have hcast : (finCongr (Nat.add_comm n N)) ((finCongr (Nat.add_comm N n)) i) = i := by
        apply Fin.ext
        rfl
      rw [hcast] at h
      exact h.symm) hS ha hw hc
  have hRel := P.optimalTerminalScalarValue_eq_of_law_equiv R (weightedMeanPermutation P wgt)
    (fun _ => rfl) hP ha hw hc
  exact he.trans ((R.optimalTerminalScalarValue_appendZeros N hR ha hw hc).trans hRel)

end ProphetSecretary.Limiting
